from datetime import datetime, date, time
from decimal import Decimal, ROUND_HALF_UP
import os
import json
import time as time_module
import contextlib
import concurrent.futures
import numpy as np
import pandas as pd
import streamlit as st
import io
import xml.etree.ElementTree as ET
from xml.dom import minidom
from reportlab.lib.pagesizes import A4, landscape
from reportlab.lib import colors
from reportlab.lib.units import cm
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, PageBreak
import yfinance as yf
import plotly.graph_objects as go
import locale
from dateutil.relativedelta import relativedelta
import hashlib
import inspect
import urllib.parse
from html import escape as _esc
try:
    from zoneinfo import ZoneInfo as _ZoneInfo
except Exception:  # Python < 3.9
    _ZoneInfo = None


def _now_paris():
    """Heure actuelle à Paris (sans fuseau attaché). Le serveur Streamlit Cloud tourne en UTC : sans cela, la
    « date du jour » et l'ouverture de la bourse seraient décalées de 1 à 2 h."""
    try:
        return pd.Timestamp.now(tz=_ZoneInfo("Europe/Paris")).tz_localize(None)
    except Exception:
        return pd.Timestamp.now()


def _today_paris():
    return _now_paris().normalize()


def _marche_ouvert_aujourdhui():
    """Euronext Paris : séance du lundi au vendredi, ouverture à 9 h (heure de Paris)."""
    n = _now_paris()
    return n.weekday() < 5 and n.hour >= 9
try:
    import doc_import as di  # lecture des avis d'opéré / relevés (fichier doc_import.py à côté de ce script)
    _IMPORT_ERR = None
except Exception as _e:  # module absent ou dépendance manquante : l'appli démarre quand même, sans l'encart d'import
    di = None
    _IMPORT_ERR = f"{type(_e).__name__}: {_e}"

# Compatibilité st.dialog (renommé depuis st.experimental_dialog selon les versions de Streamlit)
_dialog_decorator = getattr(st, "dialog", None) or getattr(st, "experimental_dialog", None)

try:
    _DIALOG_SUPPORTS_DISMISS = _dialog_decorator is not None and "on_dismiss" in inspect.signature(_dialog_decorator).parameters
except Exception:
    _DIALOG_SUPPORTS_DISMISS = False

def dialog_wrapper(title, width="small", on_dismiss=None):
    """Ouvre une fenêtre modale (st.dialog / st.experimental_dialog selon la version
    de Streamlit installée). Si aucune des deux n'est disponible (version trop ancienne),
    on retombe simplement sur un affichage inline avec un message d'information.
    width="large" agrandit la fenêtre (utile pour un formulaire à plusieurs colonnes) ; si la
    version de Streamlit installée ne connaît pas encore ce paramètre, il est simplement
    ignoré (fenêtre à la taille par défaut) plutôt que de faire planter toute l'application."""
    if _dialog_decorator is not None:
        kwargs = {"width": width}
        # on_dismiss (Streamlit récent) : permet de savoir quand l'utilisateur ferme la fenêtre avec la croix
        if on_dismiss is not None and _DIALOG_SUPPORTS_DISMISS:
            kwargs["on_dismiss"] = on_dismiss
        try:
            return _dialog_decorator(title, **kwargs)
        except TypeError:
            return _dialog_decorator(title)

    def _fallback_decorator(func):
        def _wrapped(*args, **kwargs):
            st.info("⚠️ Fenêtres modales indisponibles (mettez à jour Streamlit : `pip install -U streamlit`). Formulaire affiché ci-dessous.")
            return func(*args, **kwargs)
        return _wrapped
    return _fallback_decorator

# Compatibilité st.fragment (st.experimental_fragment sur les versions plus anciennes de
# Streamlit). SANS CECI : Streamlit relance l'intégralité du script à CHAQUE interaction avec
# un widget, y compris à l'intérieur d'une fenêtre modale (ex. choisir "Achat" dans le menu
# déroulant du formulaire "Nouvelle opération"). Or tout le haut du script recalcule à chaque
# fois les indicateurs du portefeuille (cours en direct via yfinance) et, plus bas, tout
# l'historique quotidien du portefeuille (lui aussi basé sur des cours interrogés en direct) :
# c'est cette ré-exécution complète, à chaque clic dans le formulaire, qui rendait l'ouverture
# et la saisie d'une opération très lentes. En enveloppant le bloc bouton+formulaire dans un
# st.fragment, les interactions widgets FAITES À L'INTÉRIEUR de ce bloc (changer le type
# d'opération, remplir un champ...) ne relancent plus que ce petit bloc, et non tout le
# tableau de bord. Le st.rerun() explicite appelé après l'enregistrement réussi d'une
# opération continue, lui, par défaut, à relancer TOUTE l'application (nécessaire pour que les
# totaux et graphiques se mettent bien à jour avec la nouvelle transaction).
_fragment_decorator = getattr(st, "fragment", None) or getattr(st, "experimental_fragment", None)

def fragment_wrapper(func):
    """Applique st.fragment si disponible ; sinon, retombe sur la fonction telle quelle
    (comportement identique à avant, juste sans le gain de rapidité, pour ne jamais planter
    sur une version de Streamlit trop ancienne ne connaissant pas st.fragment)."""
    if _fragment_decorator is not None:
        return _fragment_decorator(func)
    return func

def _rerun_scoped():
    """Comme st.rerun(), mais ne relance que le st.fragment en cours (scope="fragment") au lieu
    de toute l'application, quand la fonction appelante tourne dans un tel fragment (cf.
    fragment_wrapper). À utiliser pour les actions qui n'ont besoin de rafraîchir qu'une petite
    partie du dashboard sans aucun impact ailleurs (ex. ajouter/modifier/supprimer une valeur de
    la watchlist : contrairement à une transaction achat/vente, ça ne change ni les totaux ni
    aucun graphique du reste de l'app — un st.rerun() classique y relançait donc tout pour rien,
    d'où la lenteur ressentie). Retombe silencieusement sur un st.rerun() classique (comportement
    d'avant, relance toute l'app) si le paramètre scope= n'est pas disponible (version de
    Streamlit trop ancienne) ou ne peut pas s'appliquer dans ce contexte précis."""
    try:
        st.rerun(scope="fragment")
    except Exception:
        st.rerun()

# ==========================================
# CONFIGURATION & INITIALISATION
# ==========================================
st.set_page_config(
    page_title="Tableau de Bord PEA", page_icon="📈", layout="wide"
)

# ==========================================
# PERSISTANCE VIA SUPABASE (table app_storage : colonnes key / value(jsonb) / updated_at)
# ==========================================
# Remplace l'ancienne persistance locale (transactions.csv + config_pea.json), qui ne
# survivait pas aux redémarrages de l'app sur Streamlit Community Cloud (disque éphémère).
# Toutes les données passent maintenant par 2 lignes de la table "app_storage" :
#   - key="config"       -> value = dict de configuration (comme l'ancien config_pea.json)
#   - key="transactions" -> value = liste de dicts (une ligne par transaction, comme l'ancien CSV)

def _personal_mode():
    """Mode perso : activé uniquement si les secrets de l'app contiennent PERSONAL_USER_ID
    ET SUPABASE_SERVICE_KEY (donc uniquement sur votre déploiement privé, jamais sur le public)."""
    try:
        return bool(st.secrets.get("PERSONAL_USER_ID")) and bool(st.secrets.get("SUPABASE_SERVICE_KEY"))
    except Exception:
        return False

def get_supabase_client():
    """Client Supabase : un par session de navigateur (st.session_state), PAS un cache
    partagé pour tout le serveur (st.cache_resource) — sinon tous les visiteurs du site
    partageraient la même connexion/le même compte, ce qui mélangerait leurs données.

    auto_refresh_token=False : sans cela, la bibliothèque renouvelle le jeton en arrière-plan
    (thread) et Supabase ROTE alors le refresh token — l'ancien devient invalide. Le cookie du
    navigateur, lui, garderait l'ancien jeton : à la visite suivante, la reconnexion automatique
    échouait et le code par e-mail était redemandé. Ici, le renouvellement n'a lieu que dans
    _sync_auth_cookies(), qui réécrit immédiatement le cookie avec les nouveaux jetons."""
    if "_sb_client" not in st.session_state:
        from supabase import create_client
        url = st.secrets["SUPABASE_URL"]
        # Mode perso : clé service_role (accès direct, sans connexion). Sinon : clé publique habituelle.
        key = st.secrets["SUPABASE_SERVICE_KEY"] if _personal_mode() else st.secrets["SUPABASE_KEY"]
        options = None
        try:
            try:
                from supabase import ClientOptions
            except ImportError:
                from supabase.lib.client_options import ClientOptions
            options = ClientOptions(auto_refresh_token=False, persist_session=False)
        except Exception:
            options = None  # version inattendue : on retombe sur le comportement par défaut
        st.session_state["_sb_client"] = create_client(url, key, options=options) if options else create_client(url, key)
    return st.session_state["_sb_client"]

_COOKIE_MAX_AGE = 60 * 60 * 24 * 182  # ~6 mois

def _write_auth_cookies(access, refresh, max_age=_COOKIE_MAX_AGE):
    """Écrit (ou efface, avec max_age=0) les cookies de session dans le navigateur, via un petit
    script exécuté dans le navigateur. IMPORTANT : ne jamais appeler st.rerun() juste après —
    le script n'a alors pas le temps de s'exécuter et le cookie n'est jamais écrit (c'était la
    cause probable de la reconnexion demandée à chaque visite)."""
    import streamlit.components.v1 as components
    a, r = json.dumps(access or ""), json.dumps(refresh or "")
    components.html(
        f"""<script>
        (function() {{
          try {{
            var doc = window.parent.document;
            var secure = (window.parent.location.protocol === 'https:') ? '; Secure' : '';
            function setCookie(n, v, age) {{
              doc.cookie = n + '=' + encodeURIComponent(v) + '; Max-Age=' + age + '; Path=/; SameSite=Lax' + secure;
            }}
            setCookie('sb_access_token', {a}, {int(max_age)});
            setCookie('sb_refresh_token', {r}, {int(max_age)});
          }} catch (e) {{}}
        }})();
        </script>""",
        height=0,
    )

def _read_auth_cookies():
    """Lit les cookies envoyés par le navigateur avec la requête (st.context.cookies, Streamlit
    >= 1.37) : disponible immédiatement, sans attendre un composant (plus de course au démarrage).
    Retourne None seulement si on doit attendre l'ancien composant (Streamlit plus ancien)."""
    ctx = getattr(st, "context", None)
    cookies = getattr(ctx, "cookies", None) if ctx is not None else None
    if cookies is not None:
        def _get(name):
            v = cookies.get(name)
            return urllib.parse.unquote(v).strip('"') if v else ""
        return {"sb_access_token": _get("sb_access_token"), "sb_refresh_token": _get("sb_refresh_token")}
    # Repli pour Streamlit < 1.37 : ancien composant
    from streamlit_extras.cookie_manager import cookie_manager
    cm = cookie_manager()
    if not cm.ready():
        return None
    return {"sb_access_token": cm.get("sb_access_token") or "", "sb_refresh_token": cm.get("sb_refresh_token") or ""}

def _sync_auth_cookies(sb):
    """À chaque exécution : (1) obtient la session à jour (get_session renouvelle le jeton s'il est
    expiré) ; (2) si les jetons ont changé depuis ce que détient le navigateur, réécrit les cookies.
    C'est ce qui garde le cookie valide malgré la rotation des refresh tokens de Supabase."""
    try:
        sess = sb.auth.get_session()
    except Exception:
        return
    if not sess:
        return
    current = (sess.access_token, sess.refresh_token)
    if st.session_state.get("_sb_cookie_written") != current:
        _write_auth_cookies(*current)
        st.session_state["_sb_cookie_written"] = current

def _require_login():
    """Bloque l'accès au dashboard tant que la personne n'est pas connectée. Connexion sans
    mot de passe : code à 6 chiffres reçu par e-mail. Ensuite, un cookie (~6 mois) reconnecte
    automatiquement aux visites suivantes, y compris après un simple rafraîchissement de la page."""
    sb = get_supabase_client()

    if st.session_state.get("_sb_user_id"):
        _sync_auth_cookies(sb)
        return  # déjà connecté(e) pour cette session de navigateur

    cookies = _read_auth_cookies()
    if cookies is None:
        st.stop()  # ancien composant pas encore prêt : prochain rerun automatique

    if not st.session_state.get("_sb_cookie_login_tried"):
        st.session_state["_sb_cookie_login_tried"] = True
        acc, ref = cookies.get("sb_access_token"), cookies.get("sb_refresh_token")
        if ref:
            try:
                res = sb.auth.set_session(acc or "", ref)
                st.session_state["_sb_user_id"] = res.user.id
                st.session_state["_sb_user_email"] = res.user.email
                st.session_state["_sb_cookie_written"] = (acc, ref)  # ce que le navigateur détient déjà
                _sync_auth_cookies(sb)  # si le jeton a été renouvelé : réécrit le cookie
                return
            except Exception:
                _write_auth_cookies("", "", 0)  # cookie périmé/invalide : on le supprime proprement

    login_box = st.empty()
    with login_box.container():
        st.title("📈 Tableau de Bord PEA")
        st.subheader("Connexion")
        email = st.text_input("Adresse email", key="_login_email")

        if st.button("Recevoir un code de connexion", key="_login_send"):
            try:
                sb.auth.sign_in_with_otp({"email": email})
                st.session_state["_login_otp_sent_to"] = email
                st.success("Code envoyé — vérifie ta boîte mail (et tes spams).")
            except Exception as e:
                st.error(f"Erreur lors de l'envoi : {e}")

        otp_target = st.session_state.get("_login_otp_sent_to")
        verified = False
        if otp_target:
            st.caption(f"Code envoyé à {otp_target}")
            code = st.text_input("Code reçu par email (6 chiffres)", key="_login_code")
            if st.button("Valider le code", key="_login_verify"):
                try:
                    res = sb.auth.verify_otp({"email": otp_target, "token": code, "type": "email"})
                    sb.auth.set_session(res.session.access_token, res.session.refresh_token)
                    st.session_state["_sb_user_id"] = res.user.id
                    st.session_state["_sb_user_email"] = res.user.email
                    verified = True
                except Exception as e:
                    st.error(f"Code invalide ou expiré : {e}")

    if verified:
        login_box.empty()          # retire l'écran de connexion
        _sync_auth_cookies(sb)     # écrit les cookies SANS st.rerun() derrière
        return                     # la suite du script (dashboard) s'exécute dans ce même passage

    st.stop()

def _logout_button():
    with st.sidebar:
        st.caption(f"Connecté : {st.session_state.get('_sb_user_email', '')}")
        if st.button("Se déconnecter"):
            for k in ["_sb_client", "_sb_user_id", "_sb_user_email", "_login_otp_sent_to",
                      "_sb_cookie_login_tried", "_sb_cookie_written"]:
                st.session_state.pop(k, None)
            _write_auth_cookies("", "", 0)
            st.session_state["_sb_cookie_login_tried"] = True  # ne pas se reconnecter avec l'ancien cookie ce coup-ci
            import time as _t
            _t.sleep(0.6)  # laisse le script du navigateur effacer les cookies avant le rerun
            st.rerun()

if _personal_mode():
    # Lien perso : pas de connexion, mais un code d'accès dans l'URL (?k=...) pour que le lien ne soit pas ouvert à tous
    if st.query_params.get("k") != st.secrets.get("PERSONAL_ACCESS_KEY"):
        st.error("Accès refusé.")
        st.stop()
    st.session_state["_sb_user_id"] = st.secrets["PERSONAL_USER_ID"]
    st.session_state["_sb_user_email"] = "(mode perso)"
else:
    _require_login()
    _logout_button()
_current_user_id = st.session_state["_sb_user_id"]

# Clés dont la LECTURE a échoué (Supabase injoignable) pendant cette exécution : on refuse alors toute
# ÉCRITURE de cette clé, sinon l'app enregistrerait la valeur par défaut (vide) par-dessus vos vraies
# données (watchlist, transactions, réglages...) dès la première sauvegarde automatique.
_SUPABASE_LOAD_FAILED = set()

def _supabase_get_value(key_name, default):
    """Lit la valeur (colonne jsonb) associée à `key_name` POUR L'UTILISATEUR CONNECTÉ dans
    app_storage. Ne fait jamais planter l'app : si Supabase est injoignable ou que la ligne
    n'existe pas encore, renvoie `default` (comportement identique à l'ancien "fichier absent
    -> valeur par défaut")."""
    try:
        sb = get_supabase_client()
        res = (
            sb.table("app_storage")
            .select("value")
            .eq("key", key_name)
            .eq("user_id", _current_user_id)
            .execute()
        )
        _SUPABASE_LOAD_FAILED.discard(key_name)
        if res.data:
            return res.data[0]["value"]
    except Exception:
        _SUPABASE_LOAD_FAILED.add(key_name)
    return default

def _supabase_set_value(key_name, value):
    """Enregistre (upsert) la valeur associée à `key_name` POUR L'UTILISATEUR CONNECTÉ dans
    app_storage. Renvoie (True, None) en cas de succès, (False, message_erreur) sinon — même
    contrat que les anciennes fonctions save_*_csv/save_config, pour ne rien changer côté
    appelants."""
    if key_name in _SUPABASE_LOAD_FAILED:
        return False, ("Enregistrement bloqué : la lecture de vos données a échoué (connexion Supabase), "
                       "les écraser avec une valeur vide serait dangereux. Rechargez la page.")
    try:
        sb = get_supabase_client()
        sb.table("app_storage").upsert(
            {"user_id": _current_user_id, "key": key_name, "value": value}
        ).execute()
        return True, None
    except Exception as e:
        return False, f"Erreur lors de l'enregistrement dans Supabase : {e}"

def save_transactions_csv(df, path=None):
    """Nom conservé pour ne pas avoir à modifier tous les appels existants, mais enregistre
    désormais les transactions dans Supabase (clé "transactions") plutôt que dans un CSV
    local. Les dates sont converties en texte ISO et les NaN en None, pour être sérialisables
    en JSON (format attendu par la colonne jsonb de Supabase)."""
    try:
        df_to_save = df.copy()
        for col in df_to_save.columns:
            if pd.api.types.is_datetime64_any_dtype(df_to_save[col]):
                df_to_save[col] = df_to_save[col].dt.strftime("%Y-%m-%d %H:%M:%S")
        df_to_save = df_to_save.where(pd.notnull(df_to_save), None)
        records = df_to_save.to_dict(orient="records")
        return _supabase_set_value("transactions", records)
    except Exception as e:
        return False, f"Erreur lors de l'enregistrement : {e}"

def load_config():
    return _supabase_get_value(
        "config",
        {"broker": "", "yearly_target": 10000, "taux_prelevements_sociaux": 18.6}
    )

def save_config(config_data):
    return _supabase_set_value("config", config_data)

app_config = load_config()

# --- Pop-up de premier lancement : demande le nom de l'utilisateur et son courtier avant
# d'afficher le dashboard. Ne s'affiche qu'une seule fois : dès que "user_name" est enregistré
# dans la config (config_pea.json), ce bloc ne se déclenche plus jamais, même après redémarrage
# de l'app (persisté sur disque comme le reste de la config). ---
if not app_config.get("user_name"):
    @dialog_wrapper("👋 Bienvenue sur votre Tableau de Bord PEA")
    def _dialog_premier_lancement():
        st.markdown("Avant d'afficher votre dashboard, quelques informations rapides :")
        with st.form("form_premier_lancement"):
            _fl_nom = st.text_input("Quel est votre nom ?", placeholder="Ex : Marie")
            _fl_courtier = st.text_input("Quel est votre courtier ?", placeholder="Ex : Boursorama, Trade Republic...")
            if st.form_submit_button("Valider", type="primary", use_container_width=True):
                if not _fl_nom.strip():
                    st.error("Merci de renseigner votre nom pour continuer.")
                else:
                    app_config["user_name"] = _fl_nom.strip()
                    app_config["broker"] = _fl_courtier.strip()
                    _ok_fl, _err_fl = save_config(app_config)
                    if _ok_fl:
                        st.rerun()
                    else:
                        st.error(_err_fl)
    _dialog_premier_lancement()
    st.stop()

# Style CSS moderne incluant l'amélioration visible des onglets et la hauteur des tableaux ciblés
st.markdown(
    """
    <style>
    @import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&family=Manrope:wght@500;600;700;800&display=swap');

    html, body, [class*="css"], .stApp, .stMarkdown, .stDataFrame, button, input, select, textarea {
        font-family: 'Inter', -apple-system, BlinkMacSystemFont, sans-serif !important;
    }

    .stApp {
        background:
            radial-gradient(circle at 8% 8%, rgba(2, 132, 199, 0.10) 0%, transparent 45%),
            radial-gradient(circle at 92% 18%, rgba(124, 58, 237, 0.08) 0%, transparent 45%),
            radial-gradient(circle at 15% 92%, rgba(13, 148, 136, 0.08) 0%, transparent 45%),
            linear-gradient(180deg, #f8fafc 0%, #eef2f7 100%);
        color: #1e293b;
        background-attachment: fixed;
    }
    /* Bandeau coloré en haut de page */
    [data-testid="stAppViewContainer"] > .main::before {
        content: "";
        display: block;
        height: 6px;
        width: 100%;
        background: linear-gradient(90deg, #0284c7, #7c3aed, #0d9488, #0284c7);
        background-size: 300% 100%;
        animation: gradientShift 10s ease infinite;
        border-radius: 0 0 8px 8px;
        margin-bottom: 8px;
    }
    @keyframes gradientShift {
        0% { background-position: 0% 50%; }
        50% { background-position: 100% 50%; }
        100% { background-position: 0% 50%; }
    }

    /* Indicateurs centrés sur toute la largeur (Performance annuelle moyenne, Rendement des dividendes) */
    .st-key-center_metric_perf_an [data-testid="stMetric"], .st-key-center_metric_rend_div [data-testid="stMetric"],
    .st-key-center_metric_perf_an [data-testid="metric-container"], .st-key-center_metric_rend_div [data-testid="metric-container"] {
        text-align: center; align-items: center; width: 100%;
    }
    .st-key-center_metric_perf_an [data-testid="stMetric"] > div, .st-key-center_metric_rend_div [data-testid="stMetric"] > div,
    .st-key-center_metric_perf_an [data-testid="stMetricLabel"], .st-key-center_metric_rend_div [data-testid="stMetricLabel"],
    .st-key-center_metric_perf_an [data-testid="stMetricValue"], .st-key-center_metric_rend_div [data-testid="stMetricValue"],
    .st-key-center_metric_perf_an [data-testid="stMetricDelta"], .st-key-center_metric_rend_div [data-testid="stMetricDelta"] {
        justify-content: center; text-align: center; margin-left: auto; margin-right: auto;
    }

    /* Tous les indicateurs des sections Performances / Plus-values : texte, chiffre et flèche centrés dans leur colonne */
    .st-key-row_perf_wrap [data-testid="stMetric"], .st-key-row_gains_wrap [data-testid="stMetric"], .st-key-row_capital_wrap [data-testid="stMetric"],
    .st-key-row_perf_wrap [data-testid="metric-container"], .st-key-row_gains_wrap [data-testid="metric-container"], .st-key-row_capital_wrap [data-testid="metric-container"],
    .st-key-row_perf_wrap [data-testid="stMetric"] > div, .st-key-row_gains_wrap [data-testid="stMetric"] > div, .st-key-row_capital_wrap [data-testid="stMetric"] > div {
        text-align: center !important; align-items: center !important; justify-content: center !important;
    }
    .st-key-row_perf_wrap [data-testid="stMetricLabel"], .st-key-row_gains_wrap [data-testid="stMetricLabel"], .st-key-row_capital_wrap [data-testid="stMetricLabel"],
    .st-key-row_perf_wrap [data-testid="stMetricLabel"] > div, .st-key-row_gains_wrap [data-testid="stMetricLabel"] > div, .st-key-row_capital_wrap [data-testid="stMetricLabel"] > div,
    .st-key-row_perf_wrap [data-testid="stMetricValue"], .st-key-row_gains_wrap [data-testid="stMetricValue"], .st-key-row_capital_wrap [data-testid="stMetricValue"],
    .st-key-row_perf_wrap [data-testid="stMetricValue"] > div, .st-key-row_gains_wrap [data-testid="stMetricValue"] > div, .st-key-row_capital_wrap [data-testid="stMetricValue"] > div {
        display: flex !important; justify-content: center !important; text-align: center !important; width: 100% !important;
    }
    .st-key-row_perf_wrap [data-testid="stMetricLabel"] p, .st-key-row_gains_wrap [data-testid="stMetricLabel"] p, .st-key-row_capital_wrap [data-testid="stMetricLabel"] p {
        text-align: center !important; width: 100%;
    }
    /* Pastille € / % : largeur ajustée à son contenu (et non toute la largeur), centrée */
    .st-key-row_perf_wrap [data-testid="stMetricDelta"], .st-key-row_gains_wrap [data-testid="stMetricDelta"], .st-key-row_capital_wrap [data-testid="stMetricDelta"],
    .st-key-center_metric_perf_an [data-testid="stMetricDelta"], .st-key-center_metric_rend_div [data-testid="stMetricDelta"] {
        display: flex !important; width: fit-content !important; max-width: 100% !important; margin-left: auto !important; margin-right: auto !important;
        justify-content: center !important;
    }
    .st-key-center_metric_perf_an [data-testid="stMetricLabel"], .st-key-center_metric_rend_div [data-testid="stMetricLabel"],
    .st-key-center_metric_perf_an [data-testid="stMetricLabel"] > div, .st-key-center_metric_rend_div [data-testid="stMetricLabel"] > div {
        display: flex !important; justify-content: center !important; width: 100% !important;
    }
    .st-key-center_metric_perf_an [data-testid="stMetricLabel"] p, .st-key-center_metric_rend_div [data-testid="stMetricLabel"] p {
        text-align: center !important; width: 100%;
    }

    /* Accents de couleur par section de métriques (Vue d'ensemble) */
    .row-capital [data-testid="metric-container"],
    .st-key-row_capital_wrap [data-testid="metric-container"] { border-left-color: #0284c7; }
    .row-perf [data-testid="metric-container"],
    .st-key-row_perf_wrap [data-testid="metric-container"] { border-left-color: #7c3aed; }
    .row-gains [data-testid="metric-container"],
    .st-key-row_gains_wrap [data-testid="metric-container"] { border-left-color: #0d9488; }
    .st-key-center_metric_perf_an [data-testid="metric-container"] { border-left-color: #7c3aed; }
    .st-key-center_metric_rend_div [data-testid="metric-container"] { border-left-color: #0d9488; }
    /* La première rangée ("Capital & Investissement") avait un fond dégradé bleuté dédié
       (bandeau + cartes métriques blanches en relief) pour la distinguer des 2 autres rangées
       (Performances / Plus-values), qui n'avaient elles qu'un simple liseret de couleur à
       gauche — ce surlignage a été retiré : les 3 rangées ont maintenant exactement le même
       look, seul le liseret de couleur (ci-dessus) continue à les distinguer visuellement. */
    /* Conteneur englobant les 3 rangées de métriques de la Vue d'ensemble (voir
       .st-key-dashboard_overview_card dans le script) : mêmes styles que l'ancienne
       ".dashboard-card", désormais appliqués à un vrai conteneur qui enveloppe réellement son
       contenu, donc sans rectangle vide avant le titre "Capital & Investissement". Fond
       transparent (au lieu de blanc plein) pour laisser voir le dégradé de fond de la page au
       travers plutôt qu'un bloc blanc qui tranchait dessus ; la bordure/l'ombre légère suffit à
       délimiter la carte sans avoir besoin d'un fond opaque. */
    .st-key-dashboard_overview_card {
        background-color: transparent;
        border: 1px solid #e2e8f0;
        padding: 18px 22px;
        border-radius: 16px;
        box-shadow: 0 2px 6px 0 rgba(0, 0, 0, 0.04);
    }
    [data-testid="stSidebar"] {
        background-color: #ffffff;
        border-right: 1px solid #e2e8f0;
        box-shadow: 2px 0 8px rgba(0,0,0,0.02);
    }
    [data-testid="stSidebar"] h2 { color: #0f172a !important; }

    h1, h2, h3, .stMarkdown h1, .stMarkdown h2, .stMarkdown h3 {
        color: #0f172a !important; font-weight: 700 !important; letter-spacing: -0.025em;
    }
    .stMarkdown h1 { padding-bottom: 4px; border-bottom: 3px solid #0284c7; display: inline-block; }

    /* Scrollbars discrets */
    ::-webkit-scrollbar { width: 8px; height: 8px; }
    ::-webkit-scrollbar-track { background: transparent; }
    ::-webkit-scrollbar-thumb { background: #cbd5e1; border-radius: 8px; }
    ::-webkit-scrollbar-thumb:hover { background: #94a3b8; }

    /* Amélioration de la visibilité des onglets (St Tabs) : design épuré façon "nav" plate,
       sans le contour bleu de focus ni le trait rouge par défaut de BaseWeb (l'ancien
       indicateur natif "tab-highlight"/"tab-border", non stylé, apparaissait sous cette forme
       une fois un onglet sélectionné). On les masque totalement et on les remplace par un
       indicateur maison (barre dégradée en bas de l'onglet actif). */
    .stTabs [data-baseweb="tab-list"] {
        gap: 4px;
        background-color: transparent;
        padding: 0 0 0 0;
        border-bottom: 2px solid #e2e8f0;
    }
    .stTabs [data-baseweb="tab-highlight"],
    .stTabs [data-baseweb="tab-border"] {
        display: none !important;
    }
    .stTabs [data-baseweb="tab"] {
        height: 44px;
        background-color: transparent;
        border-radius: 10px 10px 0 0;
        color: #64748b;
        font-weight: 600;
        font-size: 0.94rem;
        padding: 0 16px;
        border: none;
        box-shadow: none;
        outline: none !important;
        position: relative;
        transition: color 0.15s ease-in-out, background-color 0.15s ease-in-out;
    }
    .stTabs [data-baseweb="tab"]:focus,
    .stTabs [data-baseweb="tab"]:focus-visible,
    .stTabs [data-baseweb="tab"]:focus-within {
        outline: none !important;
        box-shadow: none !important;
    }
    .stTabs [data-baseweb="tab"]:hover {
        background-color: #f0f9ff;
        color: #0284c7;
    }
    .stTabs [aria-selected="true"] {
        background-color: #f0f9ff !important;
        color: #0369a1 !important;
    }
    .stTabs [aria-selected="true"]::after {
        content: "";
        position: absolute;
        left: 10px;
        right: 10px;
        bottom: -2px;
        height: 3px;
        border-radius: 3px 3px 0 0;
        background: linear-gradient(90deg, #0284c7, #7c3aed);
    }
    .stTabs [data-baseweb="tab-panel"] { padding-top: 18px; }

    div[data-testid="metric-container"] {
        background-color: #ffffff; border: 1px solid #e2e8f0; border-left: 3px solid #0284c7;
        padding: 12px 16px; border-radius: 12px;
        box-shadow: 0 1px 3px 0 rgba(0, 0, 0, 0.05); transition: all 0.2s ease-in-out;
    }
    div[data-testid="metric-container"]:hover {
        box-shadow: 0 6px 14px -4px rgba(0, 0, 0, 0.12);
        border-color: #cbd5e1;
        transform: translateY(-2px);
    }
    div[data-testid="stMetricLabel"] p { font-size: 0.8rem; font-weight: 600; color: #64748b; text-transform: uppercase; letter-spacing: 0.03em; }
    div[data-testid="stMetricValue"] { font-weight: 700; color: #0f172a; font-size: 1.65rem; line-height: 1.25; }
    div[data-testid="stMetricValue"] div { font-size: 1.65rem !important; }
    div[data-testid="stMetricDelta"] { font-size: 0.85rem; font-weight: 600; }

    [data-testid="stDataFrame"] { border-radius: 12px; overflow: hidden; border: 1px solid #e2e8f0; }
    [data-testid="stDataFrame"] table { width: 100% !important; }
    [data-testid="stDataFrame"] th {
        background-color: #f1f5f9 !important;
        color: #0f172a !important;
        font-weight: 700 !important;
        text-transform: uppercase;
        font-size: 0.72rem;
        letter-spacing: 0.03em;
    }
    [data-testid="stDataFrame"] tbody tr:nth-child(even) { background-color: #f8fafc !important; }
    [data-testid="stDataFrame"] tbody tr:nth-child(odd) { background-color: #ffffff !important; }
    [data-testid="stDataFrame"] tbody tr:hover { background-color: #f0f9ff !important; }

    .streamlit-expanderHeader {
        background-color: #ffffff !important;
        border-radius: 12px !important;
        border: 1px solid #e2e8f0 !important;
        font-weight: 700 !important;
        color: #0f172a !important;
    }
    .streamlit-expanderHeader:hover { border-color: #7dd3fc !important; }
    .streamlit-expanderContent {
        border: 1px solid #e2e8f0 !important;
        border-top: none !important;
        border-radius: 0 0 12px 12px !important;
        background-color: transparent;
    }

    .dashboard-card {
        background-color: #ffffff;
        border: 1px solid #e2e8f0;
        padding: 18px 22px;
        border-radius: 16px;
        box-shadow: 0 2px 6px 0 rgba(0, 0, 0, 0.04);
        margin-bottom: 24px;
    }
    .dashboard-section-title {
        font-size: 0.82rem;
        font-weight: 700;
        color: #0284c7;
        margin-top: 4px;
        margin-bottom: 10px;
        text-transform: uppercase;
        letter-spacing: 0.06em;
    }

    .stButton > button, .stDownloadButton > button {
        border-radius: 10px !important;
        font-weight: 600 !important;
        transition: all 0.15s ease-in-out !important;
    }
    .stButton > button:hover { transform: translateY(-1px); box-shadow: 0 4px 10px rgba(0,0,0,0.1); }
    .stButton > button[kind="primary"] { background: linear-gradient(135deg, #0284c7 0%, #0369a1 100%) !important; border: none !important; }

    /* Bouton "Rafraîchir toutes les données" : même gabarit compact que "Nouvelle opération"
       (scopé via st.container(key=...)), mais en style secondaire "contour" discret, pour bien
       le distinguer visuellement de l'action principale d'ajout tout en restant cohérent avec
       le reste du template (mêmes rayons, même hauteur, mêmes transitions au survol). */
    .st-key-full_refresh_btn_wrap .stButton > button,
    .st-key-export_data_btn_wrap .stDownloadButton > button,
    .st-key-export_pdf_btn_wrap .stDownloadButton > button {
        padding: 4px 14px !important;
        font-size: 0.85rem !important;
        min-height: 34px !important;
        height: 34px !important;
        border-radius: 8px !important;
        background-color: #ffffff !important;
        border: 1px solid #cbd5e1 !important;
        color: #475569 !important;
        box-shadow: 0 1px 3px rgba(0,0,0,0.06) !important;
    }
    .st-key-full_refresh_btn_wrap .stButton > button:hover,
    .st-key-export_data_btn_wrap .stDownloadButton > button:hover,
    .st-key-export_pdf_btn_wrap .stDownloadButton > button:hover {
        border-color: #0284c7 !important;
        color: #0284c7 !important;
        background-color: #f0f9ff !important;
    }
    .st-key-full_refresh_btn_wrap { margin-top: 2px; }
    .st-key-export_data_btn_wrap { margin-top: 6px; }
    .st-key-export_pdf_btn_wrap { margin-top: 6px; }

    /* Boutons "Revenir à la moyenne historique" (simulation de croissance) : style
       discret "pilule" avec dégradé léger au survol, plus soigné que le bouton
       secondaire par défaut. */
    .st-key-btn_reset_apport_hist_wrap .stButton > button,
    .st-key-btn_reset_perf_hist_wrap .stButton > button {
        padding: 4px 12px !important;
        font-size: 0.78rem !important;
        min-height: 30px !important;
        height: 30px !important;
        border-radius: 999px !important;
        background-color: #f0f9ff !important;
        border: 1px solid #bae6fd !important;
        color: #0369a1 !important;
        box-shadow: none !important;
    }
    .st-key-btn_reset_apport_hist_wrap .stButton > button:hover,
    .st-key-btn_reset_perf_hist_wrap .stButton > button:hover {
        background: linear-gradient(135deg, #0284c7 0%, #0369a1 100%) !important;
        border-color: #0284c7 !important;
        color: #ffffff !important;
        transform: translateY(-1px);
        box-shadow: 0 4px 10px rgba(2, 132, 199, 0.25) !important;
    }
    .st-key-btn_reset_apport_hist_wrap, .st-key-btn_reset_perf_hist_wrap { margin: 4px 0 2px 0; }

    div[data-baseweb="input"], div[data-baseweb="select"] { border-radius: 8px !important; }

    .stProgress > div > div > div > div { background: linear-gradient(90deg, #0284c7, #38bdf8) !important; border-radius: 8px; }

    input::-webkit-input-placeholder { color: #94a3b8; }
    .css-1544g2n span, [data-testid="InputInstructions"] span { font-size: 0px; }
    [data-testid="InputInstructions"] span::after {
        content: "Appuyez sur Entrée pour valider";
        font-size: 0.75rem;
        color: #64748b;
    }

    /* Boutons "Nouvelle opération" / "Simulation" : fixés en bas de l'écran (position sticky),
       toujours visibles quel que soit l'endroit où l'on a défilé sur le dashboard, plutôt que
       cachés tout en haut une fois qu'on a scrollé plus bas. Barre désormais étirée sur toute
       la largeur de l'écran (au lieu d'une petite carte centrée) : plus imposante, plus facile
       à repérer et à cliquer, notamment sur mobile. */
    .st-key-sticky_ops_bar {
        position: fixed !important;
        bottom: 0;
        left: 0;
        right: 0;
        z-index: 9999;
        background: rgba(255, 255, 255, 0.92) !important;
        backdrop-filter: blur(10px);
        -webkit-backdrop-filter: blur(10px);
        border-radius: 20px 20px 0 0 !important;
        border-top: 1px solid #e2e8f0 !important;
        box-shadow: 0 -6px 24px rgba(15, 23, 42, 0.12) !important;
        padding: 14px max(16px, 6vw) !important;
        width: 100% !important;
        max-width: none;
    }
    /* Les deux boutons de la barre fixe : plus hauts, plus lisibles, avec un dégradé distinct
       pour bien différencier l'action principale ("Nouvelle opération") de l'action secondaire
       ("Simulation"), tout en gardant le même gabarit pour les deux (même hauteur, même arrondi). */
    .st-key-sticky_ops_bar .stButton > button {
        height: 52px !important;
        min-height: 52px !important;
        font-size: 1rem !important;
        font-weight: 700 !important;
        border-radius: 14px !important;
        letter-spacing: 0.01em;
    }
    .st-key-sticky_ops_bar .st-key-new_op_btn_wrap .stButton > button {
        background: linear-gradient(135deg, #0284c7 0%, #0369a1 100%) !important;
        border: none !important;
        color: #ffffff !important;
        box-shadow: 0 4px 14px rgba(2, 132, 199, 0.35) !important;
        padding: 0 !important;
    }
    .st-key-sticky_ops_bar .st-key-new_op_btn_wrap .stButton > button:hover {
        transform: translateY(-2px);
        box-shadow: 0 6px 18px rgba(2, 132, 199, 0.45) !important;
    }
    .st-key-sticky_ops_bar .st-key-sim_op_btn_wrap .stButton > button {
        background: #ffffff !important;
        border: 1.5px solid #7c3aed !important;
        color: #7c3aed !important;
        box-shadow: 0 2px 8px rgba(124, 58, 237, 0.12) !important;
        padding: 0 !important;
    }
    .st-key-sticky_ops_bar .st-key-sim_op_btn_wrap .stButton > button:hover {
        background: linear-gradient(135deg, #7c3aed 0%, #6d28d9 100%) !important;
        color: #ffffff !important;
        transform: translateY(-2px);
        box-shadow: 0 6px 18px rgba(124, 58, 237, 0.35) !important;
    }
    /* Marge en bas de la page pour que le dernier contenu ne se retrouve pas caché derrière la
       barre fixe (dont la hauteur est d'environ 90-100px, boutons + padding compris). */
    .main .block-container { padding-bottom: 120px !important; }


    /* Fenêtre modale "Nouvelle opération" : épurée et moderne */
    div[data-testid="stDialog"] div[role="dialog"] {
        border-radius: 20px;
        border: 1px solid #e2e8f0;
        box-shadow: 0 20px 45px -10px rgba(15, 23, 42, 0.25);
        padding-top: 6px;
    }
    div[data-testid="stDialog"] div[role="dialog"]::before {
        content: "";
        display: block;
        height: 5px;
        width: 100%;
        margin: -1px 0 14px 0;
        border-radius: 20px 20px 0 0;
        background: linear-gradient(90deg, #0284c7, #7c3aed, #0d9488);
    }
    div[data-testid="stDialog"] h2, div[data-testid="stDialog"] h3 {
        font-weight: 800 !important;
        letter-spacing: -0.02em;
    }
    .op-card-title {
        font-size: 0.72rem;
        font-weight: 700;
        color: #64748b;
        text-transform: uppercase;
        letter-spacing: 0.05em;
        margin-bottom: 8px;
    }

    /* Encadré rouge pour les champs obligatoires du formulaire "Nouvelle opération"
       (voir st.container(key="req_...") dans dialog_saisie_operation). Le sélecteur cible
       toute clé commençant par "req_", quel que soit le type d'opération. Le conteneur
       n'entoure désormais que le champ lui-même (le titre est un élément séparé au-dessus),
       et n'est présent dans le DOM que tant que le champ est vide (cf. _req_field) : il
       disparaît donc automatiquement dès qu'une valeur est saisie ou déjà pré-remplie.
       Padding réduit au minimum + marges internes neutralisées pour que le liseret colle
       au plus près du champ, sans espace visible entre le contour rouge et le widget. */
    div[class*="st-key-req_"] {
        border: 2px solid #ef4444;
        border-radius: 10px;
        padding: 1px;
        margin-bottom: 8px;
        background-color: transparent;
    }
    div[class*="st-key-req_"] [data-testid="element-container"],
    div[class*="st-key-req_"] [data-testid="stElementContainer"],
    div[class*="st-key-req_"] [data-testid="stVerticalBlock"] {
        gap: 0 !important;
        margin: 0 !important;
        padding: 0 !important;
    }
    /* Typographie chiffrée : Manrope (géométrique, moderne) en chiffres alignés « tabulaires » pour tous
       les montants — indicateurs, cartes HTML (valeurs en gras et grandes), classes .num-mono. */
    div[data-testid="stMetricValue"], div[data-testid="stMetricValue"] div, div[data-testid="stMetricDelta"],
    .num-mono,
    [data-testid="stMarkdownContainer"] [style*="font-size:1."][style*="font-weight:7"],
    [data-testid="stMarkdownContainer"] [style*="font-size:1."][style*="font-weight:8"],
    [data-testid="stMarkdownContainer"] [style*="font-size: 1."][style*="font-weight: 7"],
    [data-testid="stMarkdownContainer"] [style*="font-size: 1."][style*="font-weight: 8"],
    [data-testid="stMarkdownContainer"] [style*="font-size:2."],
    [data-testid="stMarkdownContainer"] [style*="font-size: 2."] {
        font-family: 'Manrope', 'Inter', system-ui, -apple-system, sans-serif !important;
        font-variant-numeric: tabular-nums lining-nums;
        font-feature-settings: "tnum" 1, "lnum" 1;
        letter-spacing: -0.025em;
    }
    div[data-testid="stMetricValue"], div[data-testid="stMetricValue"] div { font-size: 1.55rem !important; font-weight: 800 !important; letter-spacing: -0.035em; }
    div[data-testid="stMetricDelta"] { font-size: 0.8rem !important; font-weight: 700 !important; }
    div[data-testid="stMetricLabel"] p { font-weight: 600; letter-spacing: 0.01em; }

    /* Cartes HTML en grille : jamais tronquées, jamais de défilement horizontal. */
    .pea-stats { display: grid; grid-template-columns: repeat(auto-fit, minmax(170px, 1fr)); gap: 8px; margin: 10px 0 6px 0; }
    .pea-stat { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 10px; padding: 8px 14px; text-align: center; }
    .pea-stat .k { font-size: 0.72rem; color: #64748b; text-transform: uppercase; font-weight: 700; letter-spacing: 0.04em; }
    .pea-stat .v { font-size: 1.05rem; font-weight: 700; color: #0f172a; margin-top: 2px; }
    .pea-pills { display: flex; flex-direction: column; gap: 6px; margin: 10px 0 6px 0; }
    .pea-pill { display: flex; justify-content: space-between; align-items: center; gap: 10px; border-radius: 10px;
                padding: 4px 12px; font-size: 0.8rem; }
    .pea-duo { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; margin: 8px 0 4px 0; }
    .pea-duo-item { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 12px; padding: 8px 8px; text-align: center; }
    .pea-duo-item .k { font-size: 0.66rem; color: #64748b; text-transform: uppercase; font-weight: 700; letter-spacing: 0.04em; }
    .pea-duo-item .v { font-size: 1.3rem; font-weight: 800; color: #0f172a; line-height: 1.25; }
    .pea-duo-item .s { font-size: 0.68rem; color: #64748b; }
    .pea-duo-item.hl { background: #f0f9ff; border-color: #7dd3fc; }
    .pea-duo-item.hl .v { font-size: 1.6rem; color: #0284c7; }
    .pea-pill b { font-weight: 800; white-space: nowrap; }
    .pea-duo.tri { grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 6px; }
    .pea-duo.tri .pea-duo-item { padding: 8px 4px; min-width: 0; }
    .pea-duo.tri .pea-duo-item .k { font-size: min(0.62rem, 2.4vw); letter-spacing: 0; line-height: 1.2; }
    .pea-duo.tri .pea-duo-item .v { font-size: min(1.1rem, 4.2vw); white-space: nowrap; }
    /* Tableaux HTML : toutes les valeurs (et les titres) centrées dans les cases. */
    .pea-tbl-wrap { overflow: auto; border: 1px solid #e2e8f0; border-radius: 10px; background: #ffffff; margin: 4px 0 8px 0; }
    .pea-tbl { border-collapse: collapse; width: 100%; font-size: 0.8rem; color: #0f172a; }
    .pea-tbl th { position: sticky; top: 0; z-index: 1; background: #f8fafc; color: #475569; text-transform: uppercase;
                  font-size: 0.68rem; font-weight: 700; letter-spacing: 0.03em; padding: 8px 8px; text-align: center;
                  white-space: nowrap; border-bottom: 1px solid #e2e8f0; }
    .pea-tbl td, .pea-tbl th.ix { text-align: center; padding: 6px 8px; white-space: nowrap; border-bottom: 1px solid #f1f5f9; }
    .pea-tbl th.ix { position: static; background: transparent; color: inherit; text-transform: none; font-size: inherit; font-weight: 600; }
    .pea-tbl .ca { display: inline-flex; align-items: baseline; gap: 0.12em; }
    .pea-tbl .ar { display: inline-block; width: 0.85em; text-align: center; }
    .pea-tbl .un { display: inline-block; width: 0.9em; text-align: left; padding-left: 0.15em; }
    .pea-tbl .rv { display: inline-block; text-align: right; font-variant-numeric: tabular-nums; }
    .pea-tbl tbody tr:nth-child(even) { background: rgba(148,163,184,0.10); }
    @media (max-width: 640px) { .pea-tbl { font-size: 0.72rem; } .pea-tbl td, .pea-tbl th { padding: 5px 5px; } }
    .pea-head { text-align: center; padding: 6px 0 2px 0; }
    .pea-head .k { font-size: 0.78rem; color: #64748b; font-weight: 600; }
    .pea-head .v { font-size: 2.3rem; font-weight: 800; color: #0f172a; line-height: 1.15; }
    .pea-head .s { font-size: 0.85rem; color: #64748b; margin-top: 2px; }
    /* Cartes annuelles cliquables (Dividendes / Frais) : au clic (ou au survol), une infobulle
       s'affiche AU-DESSUS de la carte, comme sur les cartographies mensuelles. */
    .pea-cards { display: grid; grid-template-columns: repeat(auto-fill, minmax(112px, 1fr)); gap: 10px; margin-top: 6px; }
    .pea-card { position: relative; background: #ffffff; border: 1px solid #e2e8f0; border-radius: 10px; padding: 10px 8px;
                text-align: center; cursor: pointer; outline: none; box-shadow: 0 1px 2px rgba(0,0,0,0.03);
                -webkit-tap-highlight-color: transparent; }
    .pea-card .k { font-size: 0.72rem; color: #64748b; text-transform: uppercase; font-weight: 700; letter-spacing: 0.04em; }
    .pea-card .v { font-size: 1.05rem; font-weight: 700; color: #0f172a; margin-top: 2px; }
    .pea-tip { display: none; position: absolute; bottom: calc(100% + 8px); left: 0; z-index: 50; background: #0f172a; color: #ffffff;
               border-radius: 8px; padding: 8px 12px; font-size: 0.78rem; line-height: 1.5; text-align: left; white-space: nowrap;
               box-shadow: 0 6px 18px rgba(15,23,42,0.30); pointer-events: none; }
    .pea-card:hover .pea-tip, .pea-card:focus .pea-tip { display: block; }
    @media (min-width: 641px) { .pea-card:last-child .pea-tip { left: auto; right: 0; } }

    /* ===== Affichage téléphone ===== */
    @media (max-width: 640px) {
        .main .block-container, [data-testid="stMainBlockContainer"] {
            padding-left: 0.75rem !important; padding-right: 0.75rem !important;
        }
        /* Plus aucun glissement horizontal : toute rangée de colonnes passe à la ligne, 2 colonnes par
           ligne (une colonne seule occupe toute la largeur). Les rangées « compact_cols » (champs de
           saisie) et la barre fixe du bas gardent leurs propres règles, plus spécifiques. */
        [data-testid="stHorizontalBlock"] { flex-wrap: wrap !important; gap: 0.6rem !important; }
        [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {
            flex: 1 1 calc(50% - 0.6rem) !important; min-width: calc(50% - 0.6rem) !important; width: auto !important;
        }
        .pea-stats { grid-template-columns: 1fr; }
        /* N cartes (variable --n, posée en ligne par _sim_stats) TOUJOURS sur une seule ligne : colonnes
           de largeur égale (minmax(0,1fr)), police qui s'adapte à la largeur de l'écran, pas de retour à la ligne
           des montants. */
        .pea-stats.sm { grid-template-columns: repeat(var(--n, 3), minmax(0, 1fr)); gap: 5px; }
        .pea-stats.sm .pea-stat { padding: 6px 2px; min-width: 0; }
        .pea-stats.sm .k { font-size: min(0.6rem, 2.3vw); letter-spacing: 0; line-height: 1.2; }
        .pea-stats.sm .v { font-size: min(0.9rem, 3.1vw); white-space: nowrap; }
        .pea-duo-item .v { font-size: 1.15rem; }
        .pea-duo-item.hl .v { font-size: 1.4rem; }
        .pea-head .v { font-size: 1.9rem; }
        div[class*="st-key-onecol_"] [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {
            flex: 1 1 100% !important; min-width: 100% !important;
        }
        /* Onglet Classements : paires vert / rouge TOUJOURS côte à côte (comme les camemberts). */
        div[class*="st-key-sbs_"] [data-testid="stHorizontalBlock"] { flex-wrap: nowrap !important; gap: 0.4rem !important; }
        div[class*="st-key-sbs_"] [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {
            flex: 1 1 0 !important; min-width: 0 !important; width: auto !important;
        }
        div[class*="st-key-sbs_"] [data-testid="stMarkdownContainer"] p {
            font-size: 0.8rem !important; line-height: 1.3 !important; min-height: 2.6em; margin-bottom: 0.2rem !important;
        }
        div[class*="st-key-sbs_"] .pea-card { padding: 8px 10px !important; }
        div[class*="st-key-sbs_"] .pea-card .k { font-size: 0.6rem; }
        div[class*="st-key-sbs_"] .pea-card div[style*="font-size:1.55rem"] { font-size: 1.05rem !important; }
        div[class*="st-key-sbs_"] .js-plotly-plot .ytick text,
        div[class*="st-key-sbs_"] .js-plotly-plot .barlayer text { font-size: 10px !important; }
        .pea-wl .hm { display: none; }
        .pea-wl th, .pea-wl td { padding: 5px 3px !important; font-size: 0.7rem !important; white-space: normal !important; }
        .pea-cards { grid-template-columns: repeat(3, 1fr); gap: 8px; }
        .pea-card:nth-child(3n+2) .pea-tip { left: 50%; transform: translateX(-50%); }
        .pea-card:nth-child(3n) .pea-tip { left: auto; right: 0; }
        /* Rangées de champs : réduits, côte à côte (2 par ligne) */
        div[class*="st-key-compact_cols"] [data-testid="stHorizontalBlock"] {
            flex-wrap: nowrap !important; gap: 0.5rem !important;
        }
        div[class*="st-key-compact_cols"] [data-testid="stHorizontalBlock"] > div {
            flex: 1 1 0 !important; min-width: 0 !important; width: auto !important;
        }
        div[class*="st-key-compact_cols"] input,
        div[class*="st-key-compact_cols"] [data-baseweb="select"] > div { font-size: 0.82rem !important; }
        div[class*="st-key-compact_cols"] label p { font-size: 0.74rem !important; }
        div[data-testid="stMetricValue"], div[data-testid="stMetricValue"] div { font-size: 1.2rem !important; }
        /* Vue d'ensemble : cartes 2 par ligne, et la dernière (si impaire) occupe toute la largeur
           au lieu de rester seule à moitié vide. */
        .st-key-row_perf_wrap [data-testid="stHorizontalBlock"] > [data-testid="stColumn"]:last-child:nth-child(odd),
        .st-key-row_gains_wrap [data-testid="stHorizontalBlock"] > [data-testid="stColumn"]:last-child:nth-child(odd) {
            flex: 1 1 100% !important; min-width: 100% !important;
        }
        .stTabs [data-baseweb="tab"] { padding: 0 10px; font-size: 0.85rem; }
        /* À droite : ~15 % de la largeur laissés libres pour le bouton rouge « Manage app » et la
           pastille de profil que Streamlit Community Cloud affiche par-dessus l'app (ils sont dans la
           page parente, impossibles à masquer depuis ici) — les boutons ne passent plus dessous. */
        .st-key-sticky_ops_bar { padding: 10px max(15vw, 64px) calc(10px + env(safe-area-inset-bottom, 0px)) 10px !important; }
        .st-key-sticky_ops_bar .stButton > button { height: 46px !important; min-height: 46px !important; font-size: 0.85rem !important; }
        /* Les deux boutons restent CÔTE À CÔTE sur téléphone (Streamlit les empile par défaut) :
           la barre fait ~70 px au lieu de ~230 px et ne recouvre plus le contenu. */
        .st-key-sticky_ops_bar [data-testid="stHorizontalBlock"] { flex-wrap: nowrap !important; gap: 0.5rem !important; }
        .st-key-sticky_ops_bar [data-testid="stHorizontalBlock"] > [data-testid="stColumn"] {
            min-width: 0 !important; flex: 1 1 0 !important; width: auto !important;
        }
        .st-key-sticky_ops_bar .stButton > button p {
            white-space: nowrap !important; overflow: hidden; text-overflow: ellipsis;
        }
        /* Marge basse = hauteur de la barre + zone de sécurité : le dernier graphique n'est
           plus jamais caché derrière. */
        .main .block-container, [data-testid="stMainBlockContainer"] {
            padding-bottom: calc(130px + env(safe-area-inset-bottom, 0px)) !important;
        }
    }
    </style>
    """,
    unsafe_allow_html=True,
)

# Template Plotly commun pour uniformiser l'apparence de tous les graphiques
PLOTLY_LAYOUT_DEFAULTS = dict(
    paper_bgcolor='rgba(0,0,0,0)',
    plot_bgcolor='rgba(0,0,0,0)',
    font=dict(family="Manrope, Inter, sans-serif", color="#334155", size=13),
    title_font=dict(family="Inter, sans-serif", size=16, color="#0f172a"),
    legend=dict(bgcolor='rgba(0,0,0,0)'),
    hoverlabel=dict(font_family="Manrope, Inter, sans-serif", bgcolor="#0f172a", font_color="#ffffff"),
)
PLOTLY_AXIS_DEFAULTS = dict(gridcolor="#e2e8f0", zerolinecolor="#e2e8f0", linecolor="#cbd5e1", griddash="dot")

def apply_chart_theme(fig):
    """Applique le thème visuel commun à une figure Plotly sans modifier ses données/traces."""
    fig.update_layout(**PLOTLY_LAYOUT_DEFAULTS)
    fig.update_xaxes(**PLOTLY_AXIS_DEFAULTS)
    fig.update_yaxes(**PLOTLY_AXIS_DEFAULTS)
    # Marges automatiques : les libellés d'axes ne sont jamais coupés (téléphone compris).
    fig.update_xaxes(automargin=True)
    fig.update_yaxes(automargin=True)
    # PLOTLY_LAYOUT_DEFAULTS définit title_font (style du titre) mais pas title.text : pour un
    # graphique qui ne fixe pas lui-même de titre, Plotly se retrouve avec un objet "title" à
    # moitié rempli (police définie, texte manquant), ce qui affiche littéralement le texte
    # "undefined" en haut du graphique. On force donc un texte vide dans ce cas précis, sans
    # jamais écraser un titre explicitement défini par le graphique appelant.
    if fig.layout.title.text is None:
        fig.update_layout(title=dict(text=""))
    return fig

def _hex_to_rgba(c, alpha):
    """'#06b6d4' -> 'rgba(6,182,212,alpha)' ; None si la couleur n'est pas un hexadécimal simple."""
    try:
        c = str(c).strip()
        if not c.startswith("#"):
            return None
        if len(c) == 4:
            c = "#" + "".join(ch * 2 for ch in c[1:])
        r, g, b = int(c[1:3], 16), int(c[3:5], 16), int(c[5:7], 16)
        return f"rgba({r},{g},{b},{alpha})"
    except Exception:
        return None


def _style_curves(fig):
    """Rendu des courbes/aires : dégradé sous la courbe (intense près de la courbe, fondu vers l'axe),
    grille en pointillés, ligne verticale qui suit le doigt, infobulle active sur TOUTE la hauteur
    du graphique (donc aussi en dessous de la courbe)."""
    ymax_all = None
    for t in fig.data:
        if getattr(t, "type", "") not in ("scatter", "scattergl"):
            continue
        try:
            ys = pd.to_numeric(pd.Series(list(t.y)), errors="coerce").dropna()
        except Exception:
            ys = pd.Series(dtype=float)
        if getattr(t, "fill", None) == "tozeroy" and not getattr(t, "stackgroup", None) and not ys.empty:
            col = getattr(getattr(t, "line", None), "color", None)
            top, bottom = _hex_to_rgba(col, 0.42), _hex_to_rgba(col, 0.0)
            if top and bottom:
                try:
                    t.update(
                        fillgradient=dict(
                            type="vertical", start=min(0.0, float(ys.min())), stop=float(ys.max()),
                            colorscale=[[0.0, bottom], [1.0, top]],
                        ),
                        fillcolor=top,
                    )
                except Exception:
                    pass  # plotly trop ancien pour fillgradient : on garde l'aplat d'origine
    if fig.layout.hovermode in (None, "closest"):
        fig.update_layout(hovermode="x")
    fig.update_layout(hoverdistance=-1, spikedistance=-1)
    fig.update_xaxes(
        showspikes=True, spikemode="across", spikesnap="cursor",
        spikethickness=1, spikedash="dot", spikecolor="#94a3b8",
    )


# Script injecté UNE fois dans la page : « doigt maintenu » (~0,25 s) sur un graphique → l'infobulle
# suit ensuite le doigt tout seul, sans faire défiler la page. Un glissement immédiat reste un
# défilement normal de la page. Le doigt peut être n'importe où dans la zone du graphique
# (au-dessus ou au-dessous de la courbe) : on le ramène dans la zone de survol de Plotly.
_SCRUB_JS = r"""
(function () {
  var P = window.parent;
  if (!P || P.__peaScrub2) return;
  P.__peaScrub2 = true;
  var code = '(' + function () {
    var HOLD_MS = 250, TOL = 10;
    var timer = null, pending = false, scrubbing = false, sx = 0, sy = 0, gd = null;
    function plotOf(el) { return el && el.closest ? el.closest('.js-plotly-plot') : null; }
    function layerFor(g, x, y) {
      var ls = g.querySelectorAll('.nsewdrag'), best = null, bd = 1e9;
      for (var i = 0; i < ls.length; i++) {
        var r = ls[i].getBoundingClientRect();
        var dx = x < r.left ? r.left - x : (x > r.right ? x - r.right : 0);
        var dy = y < r.top ? r.top - y : (y > r.bottom ? y - r.bottom : 0);
        var d = dx + dy;
        if (d < bd) { bd = d; best = ls[i]; }
      }
      return best;
    }
    function hover(x, y) {
      if (!gd) return;
      var l = layerFor(gd, x, y);
      if (!l) return;
      var r = l.getBoundingClientRect();
      var cx = Math.min(Math.max(x, r.left + 1), r.right - 1);
      var cy = Math.min(Math.max(y, r.top + 1), r.bottom - 1);
      l.dispatchEvent(new MouseEvent('mousemove', {
        bubbles: true, cancelable: true, view: window, clientX: cx, clientY: cy
      }));
    }
    function reset() {
      if (timer) { clearTimeout(timer); timer = null; }
      pending = false; scrubbing = false;
    }
    window.addEventListener('touchstart', function (e) {
      reset();
      if (e.touches.length !== 1) return;
      var g = plotOf(e.target);
      if (!g || !g.querySelector('.nsewdrag')) return;
      gd = g; sx = e.touches[0].clientX; sy = e.touches[0].clientY;
      pending = true;
      timer = setTimeout(function () {
        timer = null; pending = false; scrubbing = true;
        gd._dragging = false;
        if (gd._fullLayout) gd._fullLayout._dragging = false;
        if (navigator.vibrate) { try { navigator.vibrate(8); } catch (_) {} }
        hover(sx, sy);
      }, HOLD_MS);
    }, { capture: true, passive: true });
    window.addEventListener('touchmove', function (e) {
      if (e.touches.length > 1) { reset(); return; }
      var t = e.touches[0];
      if (scrubbing) {
        e.preventDefault(); e.stopPropagation();
        hover(t.clientX, t.clientY);
      } else if (pending && (Math.abs(t.clientX - sx) > TOL || Math.abs(t.clientY - sy) > TOL)) {
        reset();                              // le doigt bouge tout de suite : défilement normal
      }
    }, { capture: true, passive: false });
    ['touchend', 'touchcancel'].forEach(function (n) {
      window.addEventListener(n, function () { reset(); }, { capture: true, passive: true });
    });
    document.addEventListener('contextmenu', function (e) {
      if (plotOf(e.target)) e.preventDefault();
    });
  } + ')();';
  var s = P.document.createElement('script');
  s.textContent = code;
  P.document.head.appendChild(s);
})();
"""


# Infobulle des cartographies (graphiques marqués layout.meta == "pea-tip-top") : posée AU-DESSUS de la case
# touchée (centrée sur elle) pour que le doigt ne la cache pas. Si la case est sur la première ligne
# (pas de place au-dessus dans le graphique), elle passe en dessous.
_TIP_JS = r"""
(function () {
  var P = window.parent;
  if (!P || P.__peaTip1) return;
  P.__peaTip1 = true;
  var code = '(' + function () {
    function plotOf(el) { return el && el.closest ? el.closest('.js-plotly-plot') : null; }
    function place(gd, pt) {
      var hl = gd.querySelector('.hoverlayer .hovertext');
      var svg = gd.querySelector('.main-svg');
      if (!hl || !svg || !gd._fullLayout) return;
      var xa = gd._fullLayout.xaxis, ya = gd._fullLayout.yaxis;
      var s = svg.getBoundingClientRect();
      var cx = s.left + xa._offset + xa.d2p(pt.x);
      var cy = s.top + ya._offset + ya.d2p(pt.y);
      var ch = Math.abs(ya.d2p(1) - ya.d2p(0));
      var r = hl.getBoundingClientRect();
      var left = Math.min(Math.max(cx - r.width / 2, s.left + 4), s.right - r.width - 4);
      var top = cy - ch / 2 - r.height - 8;
      if (top < s.top + 2) top = cy + ch / 2 + 8;
      var m = /translate\(\s*([-\d.e]+)[ ,]+([-\d.e]+)\s*\)/.exec(hl.getAttribute('transform') || '');
      if (!m) return;
      hl.setAttribute('transform', 'translate(' + (parseFloat(m[1]) + left - r.left) + ',' + (parseFloat(m[2]) + top - r.top) + ')');
    }
    function arm(e) {
      var gd = plotOf(e.target);
      if (!gd || gd.__peaTipOn || !gd.layout || gd.layout.meta !== 'pea-tip-top' || !gd.on) return;
      gd.__peaTipOn = true;
      gd.on('plotly_hover', function (ev) {
        var pt = ev && ev.points && ev.points[0];
        if (!pt) return;
        setTimeout(function () { place(gd, pt); }, 0);
        requestAnimationFrame(function () { place(gd, pt); });
      });
    }
    window.addEventListener('mouseover', arm, { capture: true, passive: true });
    window.addEventListener('touchstart', arm, { capture: true, passive: true });
  } + ')();';
  var s = P.document.createElement('script');
  s.textContent = code;
  P.document.head.appendChild(s);
})();
"""


# Explication « au clic » des petits indicateurs de la Vue d'ensemble : on touche/clique l'indicateur et une
# bulle indique UNIQUEMENT comment son % est calculé (pas de bulle d'aide au survol à droite du libellé).
_METRIC_TIPS = {
    "Performance Globale": "% = gains cumulés (plus-values latentes + actées + dividendes) ÷ total des apports nets.",
    "Performance YTD": "% = gain depuis le 1er janvier (latent + actée + dividendes) ÷ valeur du portefeuille au 31 décembre précédent.",
    "Performance du Mois": "% = gain depuis le 1er du mois ÷ valeur du portefeuille à la fin du mois précédent.",
    "Performance du Jour": "% = gain du jour ÷ valeur du portefeuille à la clôture de la veille (hors apports et retraits).",
    "Performance Annuelle Moyenne": "% = (1 + performance globale) ^ (1 ÷ nombre d'années depuis l'ouverture) − 1, soit un taux annuel composé (calculé après 3 mois d'historique).",
    "Plus-Value Latente": "% = plus-value latente ÷ capital investi dans les titres encore détenus.",
    "Plus-Value Actée": "% = plus-value actée ÷ valeur totale actuelle du portefeuille (actions + cash).",
    "Dividendes Reçus": "% = dividendes nets reçus ÷ total des apports nets.",
    "Frais Totaux": "% = frais totaux (courtage + TTF) ÷ gains totaux (plus-values latentes + actées + dividendes encaissés).",
    "Rendement sur cours": "% = dividendes nets annuels (reçus ÷ nombre d'années depuis l'ouverture, après 3 mois) ÷ valeur actuelle des titres détenus (cours du jour). La flèche indique le dividende annuel moyen en €.",
    "Rendement sur coût": "% = dividendes nets annuels (reçus ÷ nombre d'années depuis l'ouverture, après 3 mois) ÷ coût de revient des titres détenus (PRU × quantités). La flèche indique le dividende annuel moyen en €.",
    "PER pondéré": "Moyenne harmonique du PER (cours ÷ bénéfice par action, 12 derniers mois) des lignes, pondérée par leur valeur actuelle. ETF et valeurs sans bénéfice exclus.",
    "P/B pondéré": "Moyenne harmonique du ratio cours ÷ valeur comptable par action, pondérée par la valeur actuelle des lignes. ETF et valeurs sans donnée exclus.",
    "PEG pondéré": "Moyenne harmonique du PEG (PER ÷ croissance attendue des bénéfices), pondérée par la valeur actuelle des lignes. Valeurs sans PEG exclues.",
    "Drawdown Maximum": "% = plus forte baisse du portefeuille depuis un sommet, calculée sur la performance quotidienne (hors apports et retraits). La flèche indique l'écart actuel par rapport au dernier sommet.",
}

_METRIC_TIP_JS = r"""
(function () {
  var P = window.parent;
  if (!P) return;
  P.__peaMetricTips = __TIPS__;
  if (P.__peaMetricTipInit) return;
  P.__peaMetricTipInit = true;
  var code = '(' + function () {
    var D = document, bubble = null;
    var st = D.createElement('style');
    st.textContent = '[data-testid="stMetric"].pea-tipable{cursor:pointer}' +
      '[data-testid="stMetric"].pea-tipable [data-testid="stMetricLabel"] p::after{content:" ⓘ";opacity:.45;font-size:.85em}' +
      '#pea-metric-bubble{position:fixed;z-index:999999;max-width:280px;padding:9px 12px;border-radius:10px;' +
      'background:#1e293b;color:#f8fafc;font:500 13px/1.4 system-ui,sans-serif;box-shadow:0 6px 20px rgba(0,0,0,.28);pointer-events:none}';
    D.head.appendChild(st);
    function labelOf(m) { var l = m.querySelector('[data-testid="stMetricLabel"]'); return l ? l.textContent.trim() : ''; }
    function mark() {
      var tips = window.__peaMetricTips || {};
      D.querySelectorAll('[data-testid="stMetric"]').forEach(function (m) {
        if (tips[labelOf(m)]) m.classList.add('pea-tipable'); else m.classList.remove('pea-tipable');
      });
    }
    function close() { if (bubble) { bubble.remove(); bubble = null; } }
    D.addEventListener('click', function (e) {
      var m = e.target.closest ? e.target.closest('[data-testid="stMetric"]') : null;
      var txt = m ? (window.__peaMetricTips || {})[labelOf(m)] : null;
      var same = bubble && m && bubble.__m === m;
      close();
      if (!txt || same) return;
      bubble = D.createElement('div'); bubble.id = 'pea-metric-bubble'; bubble.textContent = txt; bubble.__m = m;
      D.body.appendChild(bubble);
      var r = m.getBoundingClientRect(), b = bubble.getBoundingClientRect();
      var left = Math.min(Math.max(r.left + r.width / 2 - b.width / 2, 8), window.innerWidth - b.width - 8);
      var top = r.top - b.height - 8; if (top < 8) top = r.bottom + 8;
      bubble.style.left = left + 'px'; bubble.style.top = top + 'px';
    }, true);
    window.addEventListener('scroll', close, { passive: true, capture: true });
    setInterval(mark, 700); mark();
  } + ')();';
  var s = P.document.createElement('script');
  s.textContent = code;
  P.document.head.appendChild(s);
})();
"""

def _inject_metric_tips():
    """Installe (une fois) l'explication au clic des indicateurs ; met à jour les textes à chaque exécution."""
    try:
        import streamlit.components.v1 as _components
        _components.html("<script>" + _METRIC_TIP_JS.replace("__TIPS__", json.dumps(_METRIC_TIPS, ensure_ascii=False).replace("</", "<\\/")) + "</script>", height=0)
    except Exception:
        pass


def _hover_zone_trace(x_edge, y_positions, customdata, hovertemplate):
    """Barre invisible couvrant toute la largeur de chaque ligne d'un classement horizontal : l'infobulle de la
    barre s'affiche alors en survolant (ou en touchant) n'importe quel point de la ligne, même quand la barre
    visible est très courte (téléphone). À ajouter AVANT la vraie barre, avec barmode=\"overlay\"."""
    return go.Bar(
        x=[x_edge] * len(y_positions), y=list(y_positions), orientation="h",
        marker=dict(color="rgba(0,0,0,0)"), customdata=customdata, hovertemplate=hovertemplate,
        showlegend=False, cliponaxis=False,
    )


def _paired_columns(key):
    """Deux colonnes côte à côte, sur ordinateur ET sur téléphone (conteneur « sbs_* », cf. CSS « Affichage
    téléphone » : colonnes de largeur égale, titres sur 2 lignes réservées pour que les deux graphiques restent
    alignés)."""
    with st.container(key=key):
        return st.columns(2, gap="small")


def _plotly_chart(fig, **kwargs):
    """st.plotly_chart sans barre d'outils ni zoom : le graphique ne peut pas être déformé ou déplacé.
    Doigt maintenu puis glissé = l'infobulle suit le doigt sur tout le graphique (y compris sous la
    courbe) ; un glissement immédiat fait défiler la page normalement."""
    cfg = dict(kwargs.pop("config", None) or {})
    if any(getattr(t, "type", "") in ("scatter", "scattergl") for t in fig.data):
        try:
            _style_curves(fig)
        except Exception:
            pass
    fig.update_layout(dragmode=False)
    fig.update_xaxes(fixedrange=True)
    fig.update_yaxes(fixedrange=True)
    cfg.update({"scrollZoom": False, "doubleClick": False, "displayModeBar": False, "displaylogo": False})
    # Injection (une seule fois par session) du script « doigt maintenu → l'infobulle suit le doigt ».
    if not st.session_state.get("_pea_scrub_injected3"):
        st.session_state["_pea_scrub_injected3"] = True
        try:
            import streamlit.components.v1 as _components
            _components.html("<script>" + _SCRUB_JS + _TIP_JS + "</script>", height=0)
        except Exception:
            pass
    return st.plotly_chart(fig, config=cfg, **kwargs)

try:
    locale.setlocale(locale.LC_TIME, 'fr_FR.UTF-8')
except Exception:
    pass

# La locale 'fr_FR.UTF-8' n'est pas installée sur tous les environnements d'hébergement
# (Streamlit Cloud, certains serveurs Windows, etc.) : le setlocale ci-dessus échoue alors
# silencieusement (except Exception: pass) et tout strftime("%B") retombe sur la locale par
# défaut du système, le plus souvent l'anglais ("October" au lieu d'"Octobre"). Pour ne plus
# dépendre de la configuration de l'hébergeur, les noms de mois affichés dans l'app passent
# donc par cette table statique plutôt que par le strftime("%B") lié à la locale système.
_MOIS_FR = ["Janvier", "Février", "Mars", "Avril", "Mai", "Juin",
            "Juillet", "Août", "Septembre", "Octobre", "Novembre", "Décembre"]

def mois_fr(dt, with_year=True):
    """Nom du mois en français pour une date/Timestamp donnée, indépendamment de la locale
    système (voir commentaire ci-dessus). with_year=True ajoute l'année ('Octobre 2026')."""
    label = _MOIS_FR[dt.month - 1]
    return f"{label} {dt.year}" if with_year else label

_PERIODES_PRESETS = [
    "Mois en cours", "3 derniers mois", "6 derniers mois", "12 derniers mois",
    "Année en cours", "3 dernières années", "5 dernières années", "10 dernières années",
    "Tout l'historique",
]

def periode_debut(label):
    """Date de début (Timestamp) correspondant à une période prédéfinie ; None = tout l'historique.
    La période court toujours jusqu'à aujourd'hui (jour en cours inclus)."""
    today = _today_paris()
    if label == "Mois en cours":
        return today.replace(day=1)
    if label == "3 derniers mois":
        return today - relativedelta(months=3)
    if label == "6 derniers mois":
        return today - relativedelta(months=6)
    if label == "12 derniers mois":
        return today - relativedelta(months=12)
    if label == "Année en cours":
        return pd.Timestamp(today.year, 1, 1)
    if label == "3 dernières années":
        return today - relativedelta(years=3)
    if label == "5 dernières années":
        return today - relativedelta(years=5)
    if label == "10 dernières années":
        return today - relativedelta(years=10)
    return None

def _round_cash(*parts):
    """Additionne des montants et arrondit le résultat au centime, en passant par Decimal
    plutôt que par un round() flottant classique. Nécessaire car round(106.225, 2) ou même
    round(25 * 4.9354, 2) peuvent renvoyer 106.22 / 123.38 au lieu de 106.23 / 123.39 : les
    prix unitaires à 3-4 décimales, une fois multipliés par une quantité, tombent souvent sur
    une représentation binaire légèrement inférieure au vrai montant décimal (ex. 25 * 4.9354
    est stocké en mémoire comme 123.38499999999999, pas 123.385), ce que round() arrondit alors
    vers le bas. Decimal(str(x)) reconstruit la valeur décimale exacte telle qu'affichée
    (ex. \"4.9354\") avant de multiplier/arrondir, ce qui reproduit fidèlement l'arrondi au
    centime réellement appliqué par le courtier sur chaque opération.
    Utilisée par compute_cash_actuel_cached et get_portfolio_history_cached (poche espèces)
    pour que le solde espèces calculé colle exactement, centime par centime, au solde réel
    affiché par le courtier — au lieu d'accumuler ces petits résidus de sous-centime au fil de
    centaines de transactions jusqu'à créer un écart visible."""
    total = Decimal("0")
    for x in parts:
        if x:
            total += Decimal(str(x))
    return float(total.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def _montant_ordre(qty, prix, frais):
    """Montant d'un ordre (achat ou vente), arrondi au centime : Quantité × Prix Unitaire + frais
    (frais positifs pour un achat, négatifs pour une vente afin de les retrancher). Construit le
    produit qty × prix directement en Decimal (à partir de la représentation décimale exacte de
    chaque valeur, via str()) plutôt qu'en multipliant des float Python : une multiplication
    flottante comme 25 * 4.9354 est stockée en mémoire comme 123.38499999999999 (au lieu de
    123.385 exactement), ce qui fait basculer l'arrondi vers le mauvais centime. Passer par
    Decimal(str(...)) dès le départ reproduit fidèlement l'arrondi réellement appliqué par le
    courtier sur l'avis d'opéré."""
    total = Decimal(str(qty)) * Decimal(str(prix))
    if frais:
        total += Decimal(str(frais))
    return float(total.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP))


def fmt_eur(val):
    if pd.isna(val):
        return "N/A"
    return f"{val:,.2f}".replace(",", " ").replace(".", ",") + " €"

def _fmt_eur_lecteur():
    """Renvoie une fonction équivalente à fmt_eur mais qui lit le réglage « masquer les montants »
    UNE SEULE FOIS, à la création. fmt_eur relit st.session_state à chaque appel, ce qui coûte
    cher (accès verrouillé côté Streamlit) quand un tableau est mis en forme cellule par cellule :
    le tableau quotidien de l'onglet Historique fait plusieurs milliers d'appels. Le réglage ne
    peut pas changer pendant le calcul d'un même tableau, donc le résultat est identique."""
    def _fmt(val):
        if pd.isna(val):
            return "N/A"
        return f"{val:,.2f}".replace(",", " ").replace(".", ",") + " €"
    return _fmt

def fmt_price_dynamic(val, commission_pct=None, ttf_val=None, include_comm=True):
    if pd.isna(val):
        return "N/A"
    val_str_full = f"{val:.4f}"
    if val_str_full.endswith("00"):
        res = f"{val:,.2f}".replace(",", " ").replace(".", ",") + " €"
    elif val_str_full.endswith("0"):
        res = f"{val:,.3f}".replace(",", " ").replace(".", ",") + " €"
    else:
        res = f"{val:,.4f}".replace(",", " ").replace(".", ",") + " €"
    
    details = []
    if include_comm and commission_pct is not None and not np.isnan(commission_pct):
        details.append(f"{commission_pct:.2f}% comm.".replace(".", ","))
    if ttf_val is not None and not np.isnan(ttf_val) and ttf_val > 0:
        details.append(f"TTF: {ttf_val:,.2f} €".replace(",", " ").replace(".", ","))
    
    if details:
        res += f" - {', '.join(details)}"
    return res

def _dynamic_decimal_str(val):
    """Reproduit la logique d'affichage dynamique des prix du tableau de bord
    (fmt_price_dynamic ci-dessus) : 2 décimales si elles suffisent, sinon 3, sinon 4 au
    maximum — jamais plus de précision que nécessaire, mais surtout jamais moins que ce
    qu'affichent déjà les tableaux de l'application (un prix comme 12,3456 € ne doit pas être
    arrondi à 12,35 € dans les exports). Renvoie une chaîne avec point décimal (sans séparateur
    de milliers), ou None si la valeur est absente/non applicable."""
    if val is None or (isinstance(val, (float, int)) and pd.isna(val)):
        return None
    val = float(val)
    val_str_full = f"{val:.4f}"
    if val_str_full.endswith("00"):
        return f"{val:.2f}"
    elif val_str_full.endswith("0"):
        return f"{val:.3f}"
    else:
        return f"{val:.4f}"

def _qty_dynamic_str(val):
    """Reproduit l'affichage des quantités du tableau de bord (format_quantite, voir plus bas) :
    nombre entier sans décimale si la quantité est ronde (ex. 3 et non 3,0000), sinon jusqu'à 4
    décimales avec les zéros inutiles retirés à la fin (ex. 0,3333). Renvoie une chaîne avec
    point décimal (sans séparateur de milliers), ou None si la valeur est absente/non
    applicable."""
    if val is None or (isinstance(val, (float, int)) and pd.isna(val)):
        return None
    val = float(val)
    if val % 1 == 0:
        return f"{int(val)}"
    return f"{val:.4f}".rstrip("0").rstrip(".")

def _xml_date_str(dt):
    """Formatte une date au format JJ/MM/AAAA pour l'export XML, ou chaîne vide si absente."""
    return dt.strftime("%d/%m/%Y") if pd.notnull(dt) else ""

def _xml_heure_str(dt):
    """Formatte une heure au format HH:MM:SS pour l'export XML, ou chaîne vide si absente."""
    return dt.strftime("%H:%M:%S") if pd.notnull(dt) else ""

def _xml_num_str(val, unit="", dynamic=False, qty=False):
    """Formatte un nombre pour l'export XML : point décimal (format technique), avec un espace
    comme séparateur de milliers pour la lisibilité (ex. 1 000.00), et l'unité ajoutée à la fin
    du texte si fournie (ex. "1 000.00 €", "12.3456 %"), ou chaîne vide si la valeur est
    absente/nulle/non applicable. dynamic=True applique la précision variable (2 à 4 décimales)
    du tableau de bord (_dynamic_decimal_str) au lieu d'arrondir systématiquement à 2 décimales
    — à utiliser pour les prix unitaires et les facteurs de split, dont l'arrondi à 2 décimales
    peut masquer une partie de la valeur réellement enregistrée. qty=True utilise à la place le
    format des quantités du tableau de bord (_qty_dynamic_str : entier sans décimale si la
    quantité est ronde, sinon jusqu'à 4 décimales sans zéro inutile)."""
    if val is None or (isinstance(val, float) and pd.isna(val)):
        return ""
    if qty:
        dec_str = _qty_dynamic_str(val)
        decimals = len(dec_str.split(".")[1]) if dec_str and "." in dec_str else 0
    elif dynamic:
        dec_str = _dynamic_decimal_str(val)
        decimals = len(dec_str.split(".")[1]) if dec_str and "." in dec_str else 2
    else:
        decimals = 2
    num_str = f"{float(val):,.{decimals}f}".replace(",", " ")
    return f"{num_str} {unit}".strip() if unit else num_str

def _sorted_by_type(df, type_value):
    """Renvoie les lignes d'un type d'opération donné, triées chronologiquement de la plus
    récente à la plus ancienne. Utilisé à la fois par l'export XML et l'export PDF pour ne pas
    dupliquer cette logique de filtrage/tri."""
    if df is None or df.empty:
        return df.iloc[0:0] if df is not None else pd.DataFrame()
    return df[df["Type"] == type_value].sort_values("Date_Heure", ascending=False)

def generate_transactions_xml(df, valeur=0.0, cash=0.0, total_apport=0.0, performance=0.0,
                               plus_value_latente=0.0, dividende_total=0.0, frais_total=0.0):
    """Construit l'export XML complet du PEA : d'abord une synthèse globale (date/heure de
    l'export, valeur du portefeuille, cash disponible, total des apports, performance,
    plus-value latente, dividendes cumulés, frais cumulés), puis le détail de toutes les
    transactions, regroupées par type d'opération (Apports, Achats, Ventes, Dividendes, Splits,
    Retraits), chaque liste étant triée par ordre chronologique décroissant (la plus récente en
    premier). Les noms de balises reprennent ceux demandés, adaptés en snake/CamelCase sans
    espace ni accent problématique (une balise XML ne peut pas contenir d'espace)."""
    root = ET.Element("Extrait_PEA")

    # --- Synthèse globale, tout en haut de l'export ---
    _now_export = _now_paris()
    ET.SubElement(root, "Date").text = _now_export.strftime("%d-%m-%Y")
    ET.SubElement(root, "Heure").text = _now_export.strftime("%H-%M-%S")
    ET.SubElement(root, "Valeur").text = _xml_num_str(valeur, unit="€")
    ET.SubElement(root, "Cash").text = _xml_num_str(cash, unit="€")
    ET.SubElement(root, "TotalApport").text = _xml_num_str(total_apport, unit="€")
    ET.SubElement(root, "Performance").text = _xml_num_str(performance, unit="%")
    ET.SubElement(root, "PlusValueLatente").text = _xml_num_str(plus_value_latente, unit="€")
    ET.SubElement(root, "Dividende").text = _xml_num_str(dividende_total, unit="€")
    ET.SubElement(root, "Frais").text = _xml_num_str(frais_total, unit="€")

    liste_transactions = ET.SubElement(root, "Liste_Transactions")

    # --- Liste Apports ---
    liste_apports = ET.SubElement(liste_transactions, "Liste_Apports")
    for _, row in _sorted_by_type(df, "APPORT").iterrows():
        apport = ET.SubElement(liste_apports, "Apport")
        ET.SubElement(apport, "Date").text = _xml_date_str(row["Date_Heure"])
        ET.SubElement(apport, "Montant").text = _xml_num_str(row["Quantité"], unit="€")

    # --- Liste Achats ---
    liste_achats = ET.SubElement(liste_transactions, "Liste_Achats")
    for _, row in _sorted_by_type(df, "ACHAT").iterrows():
        achat = ET.SubElement(liste_achats, "Achat")
        ET.SubElement(achat, "Date").text = _xml_date_str(row["Date_Heure"])
        ET.SubElement(achat, "Heure").text = _xml_heure_str(row["Date_Heure"])
        ET.SubElement(achat, "Nom").text = str(row.get("Nom", "") or "")
        ET.SubElement(achat, "Quantite").text = _xml_num_str(row["Quantité"], unit="titres", qty=True)
        ET.SubElement(achat, "Prix").text = _xml_num_str(row["Prix Unitaire (€)"], unit="€", dynamic=True)
        ET.SubElement(achat, "Commission").text = _xml_num_str(row["Commission (€)"], unit="€")
        ET.SubElement(achat, "TTF").text = _xml_num_str(row.get("TTF (€)", None), unit="€")

    # --- Liste Ventes ---
    liste_ventes = ET.SubElement(liste_transactions, "Liste_Ventes")
    for _, row in _sorted_by_type(df, "VENTE").iterrows():
        vente = ET.SubElement(liste_ventes, "Vente")
        ET.SubElement(vente, "Date").text = _xml_date_str(row["Date_Heure"])
        ET.SubElement(vente, "Heure").text = _xml_heure_str(row["Date_Heure"])
        ET.SubElement(vente, "Nom").text = str(row.get("Nom", "") or "")
        ET.SubElement(vente, "Quantite").text = _xml_num_str(row["Quantité"], unit="titres", qty=True)
        ET.SubElement(vente, "Prix").text = _xml_num_str(row["Prix Unitaire (€)"], unit="€", dynamic=True)
        ET.SubElement(vente, "Commission").text = _xml_num_str(row["Commission (€)"], unit="€")

    # --- Liste Dividendes (pas de balise Heure) ---
    liste_dividendes = ET.SubElement(liste_transactions, "Liste_Dividendes")
    for _, row in _sorted_by_type(df, "DIVIDENDE").iterrows():
        div = ET.SubElement(liste_dividendes, "Dividende")
        ET.SubElement(div, "Date").text = _xml_date_str(row["Date_Heure"])
        ET.SubElement(div, "Nom").text = str(row.get("Nom", "") or "")
        ET.SubElement(div, "Quantite").text = _xml_num_str(row["Quantité"], unit="titres", qty=True)
        ET.SubElement(div, "MontantBrut").text = _xml_num_str(row["Prix Unitaire (€)"], unit="€")
        ET.SubElement(div, "RetenueSourceEtrangere").text = _xml_num_str(row.get("Retenue_Source_Etrangere", None), unit="€")
        ET.SubElement(div, "RemboursementCapital").text = _xml_num_str(row.get("Remboursement_Capital", None), unit="€")

    # --- Liste Splits (pas de balise Heure) ---
    liste_splits = ET.SubElement(liste_transactions, "Liste_Splits")
    for _, row in _sorted_by_type(df, "SPLIT").iterrows():
        spl = ET.SubElement(liste_splits, "Split")
        ET.SubElement(spl, "Date").text = _xml_date_str(row["Date_Heure"])
        ET.SubElement(spl, "Nom").text = str(row.get("Nom", "") or "")
        ET.SubElement(spl, "Ratio").text = _xml_num_str(row["Quantité"], dynamic=True)
        ET.SubElement(spl, "Rompu").text = _xml_num_str(row.get("Rompu", None), unit="€")
        ET.SubElement(spl, "DateRompu").text = _xml_date_str(row.get("Date_Rompus", None))

    # --- Liste Retraits ---
    liste_retraits = ET.SubElement(liste_transactions, "Liste_Retraits")
    for _, row in _sorted_by_type(df, "RETRAIT").iterrows():
        retrait = ET.SubElement(liste_retraits, "Retrait")
        ET.SubElement(retrait, "Date").text = _xml_date_str(row["Date_Heure"])
        ET.SubElement(retrait, "Montant").text = _xml_num_str(row["Quantité"], unit="€")

    # Rendu indenté et lisible (toprettyxml) plutôt qu'un XML compact sur une seule ligne.
    rough_bytes = ET.tostring(root, encoding="utf-8")
    return minidom.parseString(rough_bytes).toprettyxml(indent="  ", encoding="utf-8")

# ------------------------------------------------------------------
# Export PDF : mêmes données que l'export XML, mais mises en page en
# tableaux (vue d'ensemble, positions actives, puis une table par type
# d'opération), via reportlab (voir /mnt/skills/public/pdf/SKILL.md).
# ------------------------------------------------------------------
def _pdf_eur_str(val, dynamic=False, qty=False):
    """Formatte un nombre pour affichage dans les tableaux PDF (virgule décimale, espace pour
    les milliers), ou tiret si la valeur est absente/non applicable. Par défaut, arrondit à 2
    décimales (montants). dynamic=True applique la précision variable (2 à 4 décimales) du
    tableau de bord (_dynamic_decimal_str), à utiliser pour les prix unitaires et les facteurs
    de split, qui peuvent nécessiter plus de précision qu'un montant total sans faire perdre
    d'information par rapport à ce qu'affichent déjà les tableaux de l'application. qty=True
    utilise à la place le format des quantités du tableau de bord (_qty_dynamic_str)."""
    if val is None or (isinstance(val, (float, int)) and pd.isna(val)):
        return "—"
    if qty:
        dec_str = _qty_dynamic_str(val)
        decimals = len(dec_str.split(".")[1]) if dec_str and "." in dec_str else 0
    elif dynamic:
        dec_str = _dynamic_decimal_str(val)
        decimals = len(dec_str.split(".")[1]) if dec_str and "." in dec_str else 2
    else:
        decimals = 2
    return f"{float(val):,.{decimals}f}".replace(",", " ").replace(".", ",")

def _pdf_date_str(dt):
    return dt.strftime("%d/%m/%Y") if pd.notnull(dt) else "—"

def _pdf_heure_str(dt):
    return dt.strftime("%H:%M:%S") if pd.notnull(dt) else "—"

def _pdf_table(data_rows, col_labels, styles, col_widths=None, header_style="pdf_cell_header", cell_style="pdf_cell",
                header_bg="#0284c7", padding=4):
    """Construit une Table reportlab stylée (en-tête coloré, lignes alternées) à partir d'une
    liste de listes de valeurs déjà formatées en chaînes de caractères. header_style/cell_style
    et padding permettent de réutiliser cette fonction pour un tableau "en grand" (vue
    d'ensemble en première page) sans dupliquer toute la logique de mise en forme."""
    header = [Paragraph(f"<b>{c}</b>", styles[header_style]) for c in col_labels]
    body = [[Paragraph(str(v), styles[cell_style]) for v in row] for row in data_rows]
    table = Table([header] + body, colWidths=col_widths, repeatRows=1)
    row_bg_cmds = [
        ("BACKGROUND", (0, i), (-1, i), colors.HexColor("#f8fafc"))
        for i in range(1, len(body) + 1) if i % 2 == 0
    ]
    table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor(header_bg)),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("GRID", (0, 0), (-1, -1), 0.5, colors.HexColor("#cbd5e1")),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("TOPPADDING", (0, 0), (-1, -1), padding),
        ("BOTTOMPADDING", (0, 0), (-1, -1), padding),
        ("LEFTPADDING", (0, 0), (-1, -1), 5),
        ("RIGHTPADDING", (0, 0), (-1, -1), 5),
    ] + row_bg_cmds))
    return table

def generate_transactions_pdf(df, df_port, valeur=0.0, cash=0.0, total_apport=0.0, performance=0.0,
                               plus_value_latente=0.0, dividende_total=0.0, frais_total=0.0,
                               broker_name="", pea_opening_date_str=""):
    """Génère le PDF complet du PEA : vue d'ensemble du portefeuille, détail des positions
    actives, puis une table par type d'opération (Apports, Achats, Ventes, Dividendes, Splits,
    Retraits), dans le même ordre et avec les mêmes informations que l'export XML."""
    buffer = io.BytesIO()
    doc = SimpleDocTemplate(
        buffer, pagesize=landscape(A4),
        topMargin=1.5 * cm, bottomMargin=1.5 * cm, leftMargin=1.5 * cm, rightMargin=1.5 * cm,
    )

    base_styles = getSampleStyleSheet()
    styles = {
        "pdf_title": ParagraphStyle("pdf_title", parent=base_styles["Title"], fontSize=22, textColor=colors.HexColor("#0f172a")),
        "pdf_subtitle": ParagraphStyle("pdf_subtitle", parent=base_styles["Normal"], fontSize=9, textColor=colors.HexColor("#64748b")),
        # Titres de section (Détail des positions actives, Liste des Achats, etc.) : agrandis
        # et dans une couleur plus soutenue/contrastée pour bien se distinguer du corps du texte.
        "pdf_h2": ParagraphStyle("pdf_h2", parent=base_styles["Heading2"], fontSize=17, leading=20,
                                  textColor=colors.HexColor("#1d4ed8"), spaceBefore=14, spaceAfter=8),
        "pdf_cell": ParagraphStyle("pdf_cell", parent=base_styles["Normal"], fontSize=8, leading=10),
        "pdf_cell_header": ParagraphStyle("pdf_cell_header", parent=base_styles["Normal"], fontSize=8, leading=10, textColor=colors.white),
        # Styles "en grand" utilisés uniquement pour le tableau de la vue d'ensemble, en
        # première page (indicateurs affichés en gros, bien visibles).
        "pdf_cell_big": ParagraphStyle("pdf_cell_big", parent=base_styles["Normal"], fontSize=14, leading=18),
        "pdf_cell_big_val": ParagraphStyle("pdf_cell_big_val", parent=base_styles["Normal"], fontSize=14, leading=18, fontName="Helvetica-Bold"),
        "pdf_cell_header_big": ParagraphStyle("pdf_cell_header_big", parent=base_styles["Normal"], fontSize=13, leading=16, textColor=colors.white),
        "pdf_empty": ParagraphStyle("pdf_empty", parent=base_styles["Normal"], fontSize=9, textColor=colors.HexColor("#94a3b8")),
    }

    story = []
    story.append(Paragraph("Export PEA — Vue d'ensemble", styles["pdf_title"]))
    sous_titre = f"Généré le {_now_paris().strftime('%d/%m/%Y à %H:%M:%S')}"
    if broker_name:
        sous_titre += f" — Courtier : {broker_name}"
    if pea_opening_date_str:
        sous_titre += f" — Ouverture du PEA : {pea_opening_date_str}"
    story.append(Paragraph(sous_titre, styles["pdf_subtitle"]))
    story.append(Spacer(1, 20))

    # --- Vue d'ensemble : indicateurs en grand, seuls sur la première page ---
    overview_rows = [
        ["Valeur du portefeuille (actions)", Paragraph(_pdf_eur_str(valeur) + " €", styles["pdf_cell_big_val"])],
        ["Cash disponible", Paragraph(_pdf_eur_str(cash) + " €", styles["pdf_cell_big_val"])],
        ["Total des apports", Paragraph(_pdf_eur_str(total_apport) + " €", styles["pdf_cell_big_val"])],
        ["Performance globale", Paragraph(_pdf_eur_str(performance) + " %", styles["pdf_cell_big_val"])],
        ["Plus-value latente", Paragraph(_pdf_eur_str(plus_value_latente) + " €", styles["pdf_cell_big_val"])],
        ["Dividendes cumulés", Paragraph(_pdf_eur_str(dividende_total) + " €", styles["pdf_cell_big_val"])],
        ["Frais cumulés", Paragraph(_pdf_eur_str(frais_total) + " €", styles["pdf_cell_big_val"])],
    ]
    # Les valeurs (2e colonne) sont déjà des Paragraph avec le style gras "pdf_cell_big_val" ;
    # _pdf_table ne doit donc pas re-envelopper cette colonne dans pdf_cell_big pour la ligne
    # libellé, mais str() sur un Paragraph ne fonctionnerait pas : on construit donc la table
    # directement ici plutôt que via _pdf_table.
    _header_big = [Paragraph("<b>Indicateur</b>", styles["pdf_cell_header_big"]), Paragraph("<b>Valeur</b>", styles["pdf_cell_header_big"])]
    _body_big = [[Paragraph(lbl, styles["pdf_cell_big"]), val] for lbl, val in overview_rows]
    overview_table = Table([_header_big] + _body_big, colWidths=[10 * cm, 8 * cm])
    _row_bg_big = [
        ("BACKGROUND", (0, i), (-1, i), colors.HexColor("#f8fafc"))
        for i in range(1, len(_body_big) + 1) if i % 2 == 0
    ]
    overview_table.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1d4ed8")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("GRID", (0, 0), (-1, -1), 0.5, colors.HexColor("#cbd5e1")),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("TOPPADDING", (0, 0), (-1, -1), 10),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 10),
        ("LEFTPADDING", (0, 0), (-1, -1), 8),
        ("RIGHTPADDING", (0, 0), (-1, -1), 8),
    ] + _row_bg_big))
    story.append(overview_table)

    # --- Saut de page : le détail des positions actives démarre à la page 2 ---
    story.append(PageBreak())
    story.append(Paragraph("Détail des positions actives", styles["pdf_h2"]))
    df_actif_pdf = df_port[df_port["Quantité"] > 0.0001].copy() if (df_port is not None and not df_port.empty) else pd.DataFrame()
    if not df_actif_pdf.empty:
        df_actif_pdf = df_actif_pdf.sort_values("Performance (%)", ascending=False)
        pos_rows = [
            [
                r.get("Nom", ""), r.get("Ticker", ""),
                _pdf_eur_str(r.get("Quantité"), qty=True),
                _pdf_eur_str(r.get("PRU Net (€)"), dynamic=True) + " €",
                _pdf_eur_str(r.get("Prix Actuel (€)"), dynamic=True) + " €", _pdf_eur_str(r.get("Valeur Actuelle (€)")) + " €",
                _pdf_eur_str(r.get("Gain Latent (€)")) + " €", _pdf_eur_str(r.get("Performance (%)")) + " %",
            ]
            for _, r in df_actif_pdf.iterrows()
        ]
        story.append(_pdf_table(
            pos_rows,
            ["Nom", "Ticker", "Quantité", "PRU Net", "Prix Actuel", "Valeur Actuelle", "Gain Latent", "Performance"],
            styles,
        ))
    else:
        story.append(Paragraph("Aucune position active.", styles["pdf_empty"]))

    # --- Listes de transactions par type (mêmes données que l'export XML) ---
    # Chaque section démarre sur une nouvelle page (saut de page avant le titre) : plus
    # lisible, et notamment la "Liste des Splits" qui démarre ainsi toujours après un saut de
    # page à la suite de la "Liste des Dividendes", plutôt qu'au milieu d'une page.
    def _add_section(title, type_value, col_labels, row_builder):
        story.append(PageBreak())
        story.append(Paragraph(title, styles["pdf_h2"]))
        rows = [row_builder(r) for _, r in _sorted_by_type(df, type_value).iterrows()]
        if rows:
            story.append(_pdf_table(rows, col_labels, styles))
        else:
            story.append(Paragraph("Aucune opération de ce type.", styles["pdf_empty"]))

    _add_section(
        "Liste des Apports", "APPORT", ["Date", "Montant"],
        lambda r: [_pdf_date_str(r["Date_Heure"]), _pdf_eur_str(r["Quantité"]) + " €"],
    )
    _add_section(
        "Liste des Achats", "ACHAT",
        ["Date", "Heure", "Nom", "Quantité", "Prix", "Commission", "TTF"],
        lambda r: [
            _pdf_date_str(r["Date_Heure"]), _pdf_heure_str(r["Date_Heure"]), r.get("Nom", ""),
            _pdf_eur_str(r["Quantité"], qty=True), _pdf_eur_str(r["Prix Unitaire (€)"], dynamic=True) + " €",
            _pdf_eur_str(r["Commission (€)"]) + " €",
            (_pdf_eur_str(r.get("TTF (€)")) + " €") if pd.notnull(r.get("TTF (€)")) and r.get("TTF (€)", 0) > 0 else "—",
        ],
    )
    _add_section(
        "Liste des Ventes", "VENTE",
        ["Date", "Heure", "Nom", "Quantité", "Prix", "Commission"],
        lambda r: [
            _pdf_date_str(r["Date_Heure"]), _pdf_heure_str(r["Date_Heure"]), r.get("Nom", ""),
            _pdf_eur_str(r["Quantité"], qty=True), _pdf_eur_str(r["Prix Unitaire (€)"], dynamic=True) + " €",
            _pdf_eur_str(r["Commission (€)"]) + " €",
        ],
    )
    _add_section(
        "Liste des Dividendes", "DIVIDENDE",
        ["Date", "Nom", "Quantité", "Montant Brut", "Retenue Source", "Remb. Capital"],
        lambda r: [
            _pdf_date_str(r["Date_Heure"]), r.get("Nom", ""), _pdf_eur_str(r["Quantité"], qty=True),
            _pdf_eur_str(r["Prix Unitaire (€)"]) + " €",
            (_pdf_eur_str(r.get("Retenue_Source_Etrangere")) + " €") if pd.notnull(r.get("Retenue_Source_Etrangere")) and r.get("Retenue_Source_Etrangere", 0) > 0 else "—",
            (_pdf_eur_str(r.get("Remboursement_Capital")) + " €") if pd.notnull(r.get("Remboursement_Capital")) and r.get("Remboursement_Capital", 0) > 0 else "—",
        ],
    )
    _add_section(
        "Liste des Splits", "SPLIT",
        ["Date", "Nom", "Ratio", "Rompu", "Date Rompu"],
        lambda r: [
            _pdf_date_str(r["Date_Heure"]), r.get("Nom", ""), _pdf_eur_str(r["Quantité"], dynamic=True),
            (_pdf_eur_str(r.get("Rompu")) + " €") if pd.notnull(r.get("Rompu")) and r.get("Rompu", 0) > 0 else "—",
            _pdf_date_str(r.get("Date_Rompus")) if pd.notnull(r.get("Rompu")) and r.get("Rompu", 0) > 0 else "—",
        ],
    )
    _add_section(
        "Liste des Retraits", "RETRAIT", ["Date", "Montant"],
        lambda r: [_pdf_date_str(r["Date_Heure"]), _pdf_eur_str(r["Quantité"]) + " €"],
    )

    doc.build(story)
    buffer.seek(0)
    return buffer.getvalue()

# ------------------------------------------------------------------
# Mémoïsation des exports XML / PDF.
# st.download_button exige que les octets du fichier soient prêts AVANT le clic, donc ces deux
# fichiers étaient reconstruits en entier à CHAQUE rerun du script (validation d'une opération,
# clic sur un onglet, changement de date...) : ~0,3 s pour 300 transactions, ~1 s pour 1000, et
# surtout AVANT le reste de la page (le bouton "Nouvelle opération", les indicateurs de la vue
# d'ensemble... ne s'affichaient qu'après). Or leur contenu ne dépend que des transactions et
# des quelques chiffres de synthèse passés en paramètre : on ne les reconstruit donc que si l'un
# d'eux a changé (ou si le fichier mémorisé a plus de _EXPORT_MEMO_MAX_AGE secondes, pour que
# l'heure "Généré le ..." écrite dans le fichier reste raisonnablement fraîche). Le contenu
# des fichiers est exactement le même qu'avant ; seule l'heure d'horodatage correspond à la
# dernière (re)construction plutôt qu'au dernier rerun.
# ------------------------------------------------------------------
_EXPORT_MEMO_MAX_AGE = 600  # secondes

def _export_signature(*parts):
    """Empreinte de tout ce dont dépend un export (DataFrames hachés ligne par ligne, autres
    valeurs via leur repr). Renvoie None si le calcul échoue : l'export est alors simplement
    reconstruit à chaque fois, comme avant (aucun risque de servir un fichier périmé)."""
    import hashlib
    try:
        h = hashlib.md5()
        for p in parts:
            if isinstance(p, pd.DataFrame):
                h.update(pd.util.hash_pandas_object(p, index=True).to_numpy().tobytes())
                h.update("|".join(map(str, p.columns)).encode("utf-8"))
            else:
                h.update(repr(p).encode("utf-8"))
            h.update(b"\x00")
        return h.hexdigest()
    except Exception:
        return None

@st.cache_resource(show_spinner=False)
def _export_memo_store():
    """Dictionnaire partagé au niveau du processus Streamlit (et non de la session navigateur) :
    la mémoïsation des exports survit ainsi à un rechargement de page (F5), qui crée une NOUVELLE
    session et vidait donc l'ancienne mémoire à chaque fois."""
    return {}

def _memo_export(kind, signature, builder):
    """Renvoie (octets, horodatage_pour_nom_de_fichier). Reconstruit via builder() uniquement si
    la signature a changé, si rien n'est encore mémorisé, ou si le fichier mémorisé est trop vieux."""
    store = _export_memo_store()
    now = time_module.time()
    slot = store.get(kind)
    if (signature is not None and slot is not None and slot["sig"] == signature
            and (now - slot["ts"]) < _EXPORT_MEMO_MAX_AGE):
        return slot["data"], slot["stamp"]
    data = builder()
    stamp = _now_paris().strftime("%d-%m-%Y_%H-%M-%S")
    store[kind] = {"sig": signature, "ts": now, "data": data, "stamp": stamp}
    return data, stamp

def _streamlit_version_at_least(major, minor):
    """True si la version de Streamlit installée est >= major.minor (False en cas de doute)."""
    import re as _re
    try:
        parts = [int(x) for x in _re.findall(r"\d+", st.__version__)[:2]]
        return tuple(parts) >= (major, minor)
    except Exception:
        return False

# Depuis Streamlit 1.52, st.download_button accepte une FONCTION comme `data` : le fichier n'est
# alors généré qu'au moment du clic, et plus à chaque rerun. Les exports XML/PDF ne coûtent donc
# plus rien tant qu'on ne les télécharge pas (même juste après avoir validé une opération, où la
# mémoïsation ci-dessus ne pouvait pas aider puisque les données venaient de changer). Sur une
# version plus ancienne, on garde la mémoïsation. Mettre _DEFERRED_DOWNLOAD_ENABLED à False pour
# forcer l'ancien fonctionnement.
_DEFERRED_DOWNLOAD_ENABLED = True
_DEFERRED_DOWNLOAD = _DEFERRED_DOWNLOAD_ENABLED and _streamlit_version_at_least(1, 52)

def _export_payload(kind, signature_parts, builder):
    """Renvoie (données pour st.download_button, horodatage du nom de fichier). `builder` est un
    callable sans argument qui fabrique les octets du fichier (et n'utilise ni st ni la session,
    car Streamlit l'exécute hors du script lors d'un téléchargement différé)."""
    if _DEFERRED_DOWNLOAD:
        return builder, _now_paris().strftime("%d-%m-%Y_%H-%M-%S")
    return _memo_export(kind, _export_signature(*signature_parts), builder)

def fmt_perf(val):
    if pd.isna(val) or np.isnan(val):
        return "N/A"
    prefix = "▲ +" if val > 0 else ("▼ " if val < 0 else "▬ ")
    return f"{prefix}{val:,.2f}%".replace(",", " ").replace(".", ",")

def fmt_perf_simple(val):
    if pd.isna(val) or isinstance(val, str) and val == "N/A":
        return "N/A"
    if np.isnan(val):
        return "N/A"
    if val > 0:
        return f"▲ +{val:,.2f}%".replace(",", " ").replace(".", ",")
    elif val < 0:
        return f"▼ {val:,.2f}%".replace(",", " ").replace(".", ",")
    else:
        return "▬ 0,00%"


def _style_perf_cell(v):
    """Couleur du texte d'une cellule de performance déjà formatée (▲ vert, ▼ rouge, ▬ gris)."""
    s = str(v)
    if s.startswith("▲"):
        return "color:#16a34a; font-weight:700;"
    if s.startswith("▼"):
        return "color:#dc2626; font-weight:700;"
    return "color:#64748b; font-weight:700;"

def _arrow_sym(val, eps=0.005):
    """▲ (hausse) / ▼ (baisse) / ▬ (stable) selon le signe, avec une petite tolérance."""
    try:
        if pd.isna(val):
            return ""
    except Exception:
        pass
    return "▲" if val > eps else ("▼" if val < -eps else "▬")


def fmt_eur_arrow(val):
    """Montant signé avec flèche : ▲ +12,00 € / ▼ -12,00 € / ▬ 0,00 €."""
    if pd.isna(val):
        return "N/A"
    if val > 0.005:
        return "▲ +" + fmt_eur(val)
    if val < -0.005:
        return "▼ " + fmt_eur(val)
    return "▬ " + fmt_eur(0.0)


def _style_perf_bg_cell(v):
    """Fond léger vert / rouge (lisible) pour une cellule déjà formatée avec ▲ / ▼."""
    s = str(v)
    if s.startswith("▲"):
        return "background-color: rgba(34,197,94,0.16); color:#15803d; font-weight:700;"
    if s.startswith("▼"):
        return "background-color: rgba(239,68,68,0.14); color:#b91c1c; font-weight:700;"
    if s.startswith("=") or s.startswith("▬"):
        return "color:#64748b; font-weight:700;"
    return ""


def fmt_perf_text_only(val):
    if pd.isna(val) or np.isnan(val):
        return "N/A"
    prefix = "+" if val > 0 else ("" if val < 0 else "")
    return f"{prefix}{val:,.2f}%".replace(".", ",")


_PERF_AN_MIN_JOURS = 30  # en dessous, pas de performance annualisée (extrapolation non significative)

def _perf_annualisee(perf_pct, jours):
    """Performance annuelle moyenne (composée) d'une ligne : la performance totale ramenée à 365 jours,
    d'après le nombre de jours réellement détenus. NaN si la ligne est détenue depuis moins de _PERF_AN_MIN_JOURS jours."""
    try:
        if pd.isna(perf_pct) or pd.isna(jours) or float(jours) < _PERF_AN_MIN_JOURS:
            return np.nan
        g = 1 + float(perf_pct) / 100.0
        if g <= 0:
            return -100.0
        return (g ** (365.0 / float(jours)) - 1) * 100.0
    except Exception:
        return np.nan

def _fmt_duree_detention(jours, secondes):
    """Nombre de jours détenus ; si le temps réel de détention est < 24 h : « 1 (24 min) » ou « 1 (3h 12min) »."""
    if jours is None or pd.isna(jours):
        return "N/A"
    sec = 0 if (secondes is None or pd.isna(secondes)) else int(secondes)
    if sec < 86400:
        h, m = sec // 3600, (sec % 3600) // 60
        return f"{int(jours)} ({m} min)" if h == 0 else f"{int(jours)} ({h}h {m:02d}min)"
    return f"{int(jours)}"

# Palette dégradée à 3 paliers (vert / rouge), partagée par TOUS les tableaux du dashboard qui
# affichent un dégradé de performance (historiques mensuel/annuel ET classement des actions par
# gain), afin d'avoir exactement le même code couleur et le même nombre de teintes partout.
_GRADIENT_GREENS_BG = ['#f0fdf4', '#dcfce7', '#bbf7d0']
_GRADIENT_GREENS_TXT = ['#166534', '#166534', '#14532d']
_GRADIENT_REDS_BG = ['#fef2f2', '#fee2e2', '#fecaca']
_GRADIENT_REDS_TXT = ['#991b1b', '#991b1b', '#7f1d1d']

import re

_TBL_ZERO_RE = re.compile(r"^[▬▲▼\s+\-−]*0+([,.]0+)?\s*(€|%)?$")

def _dash_if_empty(df, eq_cols=(), sale_flag=None, sale_col="PV actées"):
    """Remplace 0, N/A et valeurs vides d'un tableau déjà formaté par un « - ».
    eq_cols : colonnes où un zéro est une vraie valeur (ex. performance) -> « = » (N/A reste « - »).
    sale_flag : tableau de booléens (une vente a eu lieu sur la période) ; dans sale_col, un zéro devient
    « = » si une vente a été actée à 0, sinon « - »."""
    def _is_empty(v):
        if v is None:
            return True
        try:
            if pd.isna(v):
                return True
        except Exception:
            pass
        return isinstance(v, str) and v.strip() in ("", "N/A", "nan", "NaN", "None")

    def _is_zero(v):
        if isinstance(v, (int, float, np.integer, np.floating)):
            return v == 0
        return bool(_TBL_ZERO_RE.match(str(v).strip()))

    def _eq_txt(v):
        # « = 0,00 € » / « = 0,00% » : le symbole égal suivi de la valeur nulle (sans flèche ni signe).
        if isinstance(v, (int, float, np.integer, np.floating)):
            return "= 0"
        return "= " + re.sub(r"^[▬▲▼\s+\-−]+", "", str(v).strip())

    out = df.copy()
    flags = None if sale_flag is None else np.asarray(sale_flag, dtype=bool)
    for col in out.columns:
        ser = out[col]
        empty = ser.map(_is_empty)
        zero = (~empty) & ser.map(_is_zero)
        if col in eq_cols:
            res = ser.mask(zero, ser.map(_eq_txt)).mask(empty, "-")
        elif flags is not None and col == sale_col:
            res = ser.mask(zero & flags, ser.map(_eq_txt)).mask((zero & ~flags) | empty, "-")
        else:
            res = ser.mask(zero | empty, "-")
        out[col] = res
    return out

def _row_styles_of(styles_df):
    """Style de ligne (une chaîne CSS par ligne) à partir d'un DataFrame de styles uniformes par ligne."""
    if styles_df is None or styles_df.shape[1] == 0:
        return None
    return [str(x) for x in styles_df.iloc[:, 0].tolist()]


_TBL_IFRAME_CSS = """
html, body { margin: 0; height: 100%; background: transparent; font-family: Manrope, Inter, system-ui, sans-serif; }
.pea-tbl-wrap { height: 100%; overflow: auto; border: 1px solid #e2e8f0; border-radius: 10px; background: #ffffff; box-sizing: border-box; }
.pea-tbl { border-collapse: separate; border-spacing: 0; width: 100%; font-size: 0.8rem; color: #0f172a; }
.pea-tbl th { position: sticky; top: 0; z-index: 2; background: #f8fafc; color: #475569; text-transform: uppercase;
              font-size: 0.68rem; font-weight: 700; letter-spacing: 0.03em; padding: 8px 8px; text-align: center;
              white-space: nowrap; border-bottom: 1px solid #e2e8f0; cursor: pointer; user-select: none; }
.pea-tbl th.s-asc::after { content: " ▲"; font-size: 0.6rem; } .pea-tbl th.s-desc::after { content: " ▼"; font-size: 0.6rem; }
.pea-tbl td, .pea-tbl th.ix { text-align: center; padding: 6px 8px; white-space: nowrap; border-bottom: 1px solid #f1f5f9; }
.pea-tbl th.ix { position: static; background: transparent; color: inherit; text-transform: none; font-size: inherit; font-weight: 600; cursor: default; }
.pea-tbl tbody tr:nth-child(even) { background: rgba(148,163,184,0.10); }
.pea-tbl tfoot td, .pea-tbl tfoot th { position: sticky; bottom: 0; z-index: 2; background: #f1f5f9; font-weight: 800;
                                       border-top: 2px solid #cbd5e1; border-bottom: none; }
.pea-tbl th.stk, .pea-tbl td.stk { position: sticky; left: 0; z-index: 3; background: #ffffff; text-align: left; font-weight: 700;
                                  box-shadow: 2px 0 4px -2px rgba(15,23,42,0.25); }
.pea-tbl tbody tr:nth-child(even) td.stk { background: #f4f6f9; }
.pea-tbl th.stk { background: #f8fafc; z-index: 4; }
.pea-tbl tfoot td.stk { background: #f1f5f9; z-index: 4; }
.pea-tbl .ca { display: inline-flex; align-items: baseline; gap: 0.12em; }
.pea-tbl .ar { display: inline-block; width: 0.85em; text-align: center; }
.pea-tbl .rv { display: inline-block; text-align: right; font-variant-numeric: tabular-nums; }
.pea-tbl .un { display: inline-block; width: 0.9em; text-align: left; padding-left: 0.15em; }
"""

_TBL_IFRAME_JS = r"""
(function () {
  var t = document.getElementById('t'); if (!t) return;
  var tb = t.tBodies[0], hr = t.tHead.rows[0];
  function key(s) {
    s = (s || '').trim();
    var m = s.match(/^(\d{2})[-\/](\d{2})[-\/](\d{4})$/); if (m) return +(m[3] + m[2] + m[1]);
    m = s.match(/^(\d{2})\/(\d{4})$/); if (m) return +(m[2] + m[1]);
    var c = s.replace(/[\u00a0\u202f\s€%▲▼▬=]/g, '').replace('\u2212', '-').replace(',', '.');
    if (/^[+\-]?\d+(\.\d+)?$/.test(c)) return parseFloat(c);
    var lead = s.match(/^(\d+)\s*\(/); if (lead) return parseFloat(lead[1]);
    return s === '-' || s === '' ? null : s.toLowerCase();
  }
  var cur = document.getElementById('cur'), wrap = document.querySelector('.pea-tbl-wrap');
  if (cur && wrap) { wrap.scrollTop = Math.max(0, cur.offsetTop - hr.offsetHeight); }
  var dir = {}, last = -1;
  Array.prototype.forEach.call(hr.cells, function (th, i) {
    if (th.className === 'ix') return;
    th.addEventListener('click', function () {
      var d = (last === i && dir[i] === 1) ? -1 : 1; dir[i] = d; last = i;
      Array.prototype.forEach.call(hr.cells, function (x) { x.classList.remove('s-asc', 's-desc'); });
      th.classList.add(d === 1 ? 's-asc' : 's-desc');
      var rows = Array.prototype.slice.call(tb.rows);
      var keys = rows.map(function (r) { return key(r.cells[i].textContent); });
      var idx = rows.map(function (_, k) { return k; });
      idx.sort(function (a, b) {
        var x = keys[a], y = keys[b];
        if (x === null && y === null) return a - b; if (x === null) return 1; if (y === null) return -1;
        if (typeof x === 'number' && typeof y === 'number') return (x - y) * d || (a - b);
        return String(x).localeCompare(String(y), 'fr') * d || (a - b);
      });
      var frag = document.createDocumentFragment();
      idx.forEach(function (k) { frag.appendChild(rows[k]); });
      tb.appendChild(frag);
    });
  });
})();
"""

_PAREN_RE = re.compile(r"^(.*?)\s?\((▲|▼|▬|=)\s?([^()]*\d[^()]*)\)$")

def _paren_cell(v, pw=0, nw=0):
    """Cellule « prix (▲ +1,20%) » : prix en couleur par défaut, seule la parenthèse est colorée ;
    prix, flèche, nombre et % occupent des positions fixes (alignés d'une ligne à l'autre)."""
    m = _PAREN_RE.match(str(v))
    if not m:
        return None
    px, ar, num = m.groups()
    col = "#16a34a" if ar == "▲" else ("#dc2626" if ar == "▼" else "#64748b")
    if ar == "▬":
        ar = "="
    unit = "%" if num.endswith("%") else ""
    num = num[:-1] if unit else num
    return ('<span class="ca">'
            f'<span class="rv" style="min-width:{pw}ch">{_esc(px)}</span>'
            f'<span style="color:{col};font-weight:700;display:inline-flex;align-items:baseline;gap:0.12em;margin-left:0.4em;">'
            f'<span>(</span><span class="ar">{ar}</span>'
            f'<span class="rv" style="min-width:{nw}ch">{_esc(num)}</span>'
            f'<span>{unit})</span></span></span>')

_CELL_RE = re.compile(r"^(?:([▲▼▬=])\s)?(.*\d.*?)\s?(€|%)?$")

def _html_table(df, row_styles=None, cell_style=None, show_index=False, index_label="N°", max_height=None, focus_row=None, total_row=None, sticky_col=None):
    """Tableau HTML avec toutes les valeurs centrées. row_styles : une chaîne CSS par ligne ;
    cell_style(colonne, valeur) -> chaîne CSS d'une cellule. Défilement interne au-delà de 25 lignes.
    Dans les colonnes qui contiennent une flèche (▲ ▼ ▬ =) ou une unité (€ %), la flèche, le nombre et l'unité
    occupent chacun une position fixe : flèches et unités sont alignées verticalement d'une ligne à l'autre.
    total_row : dict {colonne: texte déjà formaté} -> ligne « Total » figée en bas du tableau (hors tri).
    sticky_col : nom d'une colonne qui reste figée à gauche quand on fait défiler le tableau horizontalement."""
    cols = list(df.columns)
    head = ("<th>" + _esc(str(index_label)) + "</th>" if show_index else "") + "".join(
        (f'<th class="stk">{_esc(str(c))}</th>' if c == sticky_col else f"<th>{_esc(str(c))}</th>") for c in cols)
    idx = list(df.index)
    # Analyse (une seule fois) de chaque colonne : (flèche, nombre, unité) par cellule, largeur max du nombre.
    parsed, num_w, has_arrow = {}, {}, {}
    for c in cols:
        vals = df[c].astype(str).tolist()
        if total_row is not None:
            vals = vals + [str(total_row.get(c, ""))]  # la ligne Total participe à l'alignement des colonnes
        pl, w, ar, structured = [], 0, False, False
        for t in vals:
            m = _CELL_RE.match(t) if ("€" in t or "%" in t or t[:1] in "▲▼▬=") else None
            if m and (m.group(1) or m.group(3)) and not t.rstrip().endswith(")"):
                pl.append((m.group(1) or "", m.group(2), m.group(3) or ""))
                w = max(w, len(m.group(2)))
                ar = ar or bool(m.group(1))
                structured = True
            else:
                pl.append(None)
        if structured:
            parsed[c], num_w[c], has_arrow[c] = pl, w, ar
    paren_w = {}
    for c in cols:
        _ms = [_PAREN_RE.match(t) for t in (df[c].astype(str).tolist() + ([str(total_row.get(c, ""))] if total_row is not None else []))]
        _ms = [m for m in _ms if m]
        if _ms:
            paren_w[c] = (max(len(m.group(1)) for m in _ms),
                          max(len(m.group(3).rstrip("%")) for m in _ms))
    rows = []
    for i, row in enumerate(df.itertuples(index=False, name=None)):
        rs = (row_styles[i] if row_styles is not None else "") or ""
        tds = [f'<th class="ix">{_esc(str(idx[i]))}</th>'] if show_index else []
        for c, v in zip(cols, row):
            cs = (cell_style(c, v) if cell_style else "") or ""
            if str(v).startswith("= ") and "font-weight" not in cs:
                cs += "font-weight:700;"
            p = parsed[c][i] if c in parsed else None
            if p is not None:
                arrow, num, unit = p
                inner = '<span class="ca">'
                if has_arrow[c]:
                    inner += f'<span class="ar">{arrow}</span>'
                inner += f'<span class="rv" style="min-width:{num_w[c]}ch">{_esc(num)}</span>'
                if unit:
                    inner += f'<span class="un">{unit}</span>'
                inner += "</span>"
            else:
                inner = (_paren_cell(v, *paren_w[c]) if c in paren_w else None) or _esc(str(v))
            _k = ' class="stk"' if c == sticky_col else ""
            tds.append(f'<td{_k} style="{cs}">{inner}</td>' if cs else f"<td{_k}>{inner}</td>")
        _rid = ' id="cur"' if (focus_row is not None and i == focus_row) else ""
        rows.append(f'<tr{_rid} style="{rs}">' + "".join(tds) + "</tr>" if rs else f"<tr{_rid}>" + "".join(tds) + "</tr>")
    foot = ""
    if total_row is not None:
        _n_body = len(rows)
        tds = ['<th class="ix"></th>'] if show_index else []
        for c in cols:
            v = total_row.get(c, "")
            cs = (cell_style(c, v) if cell_style else "") or ""
            if str(v).startswith("= ") and "font-weight" not in cs:
                cs += "font-weight:700;"
            p = parsed[c][_n_body] if c in parsed else None
            if p is not None:
                arrow, num, unit = p
                inner = '<span class="ca">'
                if has_arrow[c]:
                    inner += f'<span class="ar">{arrow}</span>'
                inner += f'<span class="rv" style="min-width:{num_w[c]}ch">{_esc(num)}</span>'
                if unit:
                    inner += f'<span class="un">{unit}</span>'
                inner += "</span>"
            else:
                inner = (_paren_cell(v, *paren_w[c]) if c in paren_w else None) or _esc(str(v))
            _k = ' class="stk"' if c == sticky_col else ""
            tds.append(f'<td{_k} style="{cs}">{inner}</td>' if cs else f"<td{_k}>{inner}</td>")
        foot = "<tfoot><tr>" + "".join(tds) + "</tr></tfoot>"
    cap = int(max_height) if max_height else 640
    n_rows = len(rows)
    height = int(min(cap, 34 + 30 * n_rows + 14 + (36 if total_row is not None else 0)))
    doc = (f"<style>{_TBL_IFRAME_CSS}</style>"
           f'<div class="pea-tbl-wrap"><table class="pea-tbl" id="t"><thead><tr>{head}</tr></thead>'
           f'<tbody>{"".join(rows)}</tbody>{foot}</table></div><script>{_TBL_IFRAME_JS}</script>')
    try:
        import streamlit.components.v1 as _components
        _components.html(doc, height=height, scrolling=False)
    except Exception:
        st.markdown(f'<div class="pea-tbl-wrap"><table class="pea-tbl"><thead><tr>{head}</tr></thead>'
                    f'<tbody>{"".join(rows)}</tbody>{foot}</table></div>', unsafe_allow_html=True)


def _make_get_h_val(history_df):
    """Équivalent rapide de la fonction get_h_val des tableaux mensuel/annuel : renvoie
    (valeur portefeuille, apports, gain réalisé, dividendes, valeur actions, capital investi) au
    dernier jour de l'historique <= ts, ou six 0.0 si ts précède l'historique. Les colonnes sont
    extraites UNE fois en tableaux numpy et le jour est trouvé par recherche dichotomique
    (searchsorted) au lieu de refiltrer l'index avec un masque booléen à chaque appel."""
    _idx = history_df.index
    _cols = [history_df[c].to_numpy() for c in (
        "Valeur du Portefeuille (€)", "Apports Cumulés (€)", "Gain Réalisé Cumulé (€)",
        "Dividendes Cumulés (€)", "Valeur Actions (€)", "Capital Investi Total (€)")]
    def get_h_val(ts):
        pos = _idx.searchsorted(ts, side="right") - 1
        if pos < 0:
            return 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
        return tuple(c[pos] for c in _cols)
    return get_h_val

def _make_tx_period_agg(df_tx):
    """Renvoie f(annee, mois=None) -> (nb mouvements achat/vente, montant des achats, frais,
    apports) pour un mois ou une année, à partir de tableaux numpy pré-extraits : évite de
    refiltrer tout le DataFrame de transactions (et de faire un .apply ligne à ligne) à chaque
    mois/année. Les sommes portent sur les mêmes valeurs, dans le même ordre, qu'avant."""
    _dt = df_tx["Date_Heure"].dt
    _yr, _mo = _dt.year.to_numpy(), _dt.month.to_numpy()
    _type = df_tx["Type"].to_numpy()
    _qty = df_tx["Quantité"].to_numpy(dtype=float)
    _montant_achat = _qty * df_tx["Prix Unitaire (€)"].to_numpy(dtype=float)
    _frais = df_tx["Frais Totaux (€)"].to_numpy(dtype=float) if "Frais Totaux (€)" in df_tx.columns else None
    _is_achat, _is_vente, _is_apport = (_type == "ACHAT"), (_type == "VENTE"), (_type == "APPORT")
    def agg(annee, mois=None):
        m = (_yr == annee) if mois is None else ((_yr == annee) & (_mo == mois))
        nb = int(np.count_nonzero(m & (_is_achat | _is_vente)))
        achats = float(np.nansum(_montant_achat[m & _is_achat]))
        frais = float(np.nansum(_frais[m])) if _frais is not None else 0.0
        apports = float(np.nansum(_qty[m & _is_apport]))
        return nb, achats, frais, apports
    def ventes(annee, mois=None):
        """Montant brut des ventes (quantité × prix unitaire) sur le mois ou l'année."""
        m = (_yr == annee) if mois is None else ((_yr == annee) & (_mo == mois))
        return float(np.nansum(_montant_achat[m & _is_vente]))
    agg.ventes = ventes
    return agg

def get_quantile_level_styles(vals_arr):
    """Calcule, pour chaque valeur numérique d'un tableau (peu importe l'unité : %, €...), le
    style CSS (fond + texte) à 3 paliers de vert (positif) ou de rouge (négatif). Le seuillage
    est calculé par quantiles PROPRES à ce tableau dès qu'il y a assez de valeurs (>= 3) du même
    signe ; sinon, on retombe sur un ratio par rapport au maximum du même signe, pour rester
    cohérent visuellement même sur un tableau à 1 ou 2 lignes."""
    greens_bg = _GRADIENT_GREENS_BG
    greens_txt = _GRADIENT_GREENS_TXT
    reds_bg = _GRADIENT_REDS_BG
    reds_txt = _GRADIENT_REDS_TXT
    vals_arr = np.asarray(vals_arr, dtype=float)
    pos_vals = vals_arr[(~np.isnan(vals_arr)) & (vals_arr > 0)]
    neg_vals = vals_arr[(~np.isnan(vals_arr)) & (vals_arr < 0)]

    pos_seuils = np.quantile(pos_vals, [0.4, 0.75]) if pos_vals.size >= 3 else None
    neg_seuils = np.quantile(np.abs(neg_vals), [0.4, 0.75]) if neg_vals.size >= 3 else None
    max_pos = float(pos_vals.max()) if pos_vals.size > 0 else 0.0
    max_neg = float(np.abs(neg_vals).max()) if neg_vals.size > 0 else 0.0

    styles = []
    for v in vals_arr:
        if np.isnan(v) or v == 0:
            styles.append('')
            continue
        if v > 0:
            if pos_seuils is not None:
                lvl = int(np.digitize(v, pos_seuils))
            else:
                ratio = v / max(max_pos, 1e-9)
                lvl = 2 if ratio > 0.66 else (1 if ratio > 0.33 else 0)
            lvl = min(lvl, 2)
            styles.append(f'background-color: {greens_bg[lvl]}; color: {greens_txt[lvl]}; font-weight: 600;')
        else:
            av = abs(v)
            if neg_seuils is not None:
                lvl = int(np.digitize(av, neg_seuils))
            else:
                ratio = av / max(max_neg, 1e-9)
                lvl = 2 if ratio > 0.66 else (1 if ratio > 0.33 else 0)
            lvl = min(lvl, 2)
            styles.append(f'background-color: {reds_bg[lvl]}; color: {reds_txt[lvl]}; font-weight: 600;')
    return styles

def _pea_tip_html(titre, total_txt, lines, accent_color):
    """Infobulle HTML (affichée au clic/survol de la carte, au-dessus d'elle) : titre, total, puis le
    détail de la composition (« Dividende : … », « Rompu : … », « Commission : … »)."""
    rows = "".join(f"<div>{_esc(l)}</div>" for l in lines)
    return (f'<div class="pea-tip"><b style="color:{accent_color};">{_esc(str(titre))}</b>'
            f'<div>Total : <b>{_esc(total_txt)}</b></div>{rows}</div>')

def render_total_card(label, montant, accent_color, detail_source=None, detail_value_col=None, detail_kind=None):
    """Total général sous la même forme de carte que les cartes annuelles ; un clic (ou le survol)
    affiche le détail de sa composition sur l'ensemble des années."""
    tip = ""
    if detail_source is not None and detail_kind is not None:
        lines = _breakdown_lines_for_kind(detail_source, detail_kind, detail_value_col)
        if lines:
            tip = _pea_tip_html("Total général", fmt_eur(montant), lines, accent_color)
    st.markdown(
        f'<div class="pea-card" tabindex="0" style="border-left:6px solid {accent_color}; padding:14px 18px; text-align:left; '
        f'margin-bottom:4px;">'
        f'<div class="k">{label}</div>'
        f'<div style="font-size:1.55rem; font-weight:800; color:#0f172a; margin-top:3px;">{fmt_eur(montant)}</div>{tip}</div>',
        unsafe_allow_html=True
    )

def render_yearly_amounts(yearly_series, accent_color, detail_source=None, detail_value_col=None, detail_kind=None):
    """Un total par année sous forme de petites cartes (la plus récente d'abord). Un clic (ou le survol)
    sur une carte affiche, au-dessus d'elle, l'année, le total et la provenance du montant."""
    # NB : HTML construit sur une seule ligne par carte (pas d'indentation de 4 espaces ni de ligne vide :
    # Markdown l'afficherait comme du code).
    cards = []
    for an, montant in sorted(yearly_series.items(), key=lambda x: x[0], reverse=True):
        tip = ""
        if detail_source is not None and detail_kind is not None and "Date_Heure" in detail_source.columns:
            df_an = detail_source[detail_source["Date_Heure"].dt.year == an]
            lines = _breakdown_lines_for_kind(df_an, detail_kind, detail_value_col)
            if lines:
                tip = _pea_tip_html(an, fmt_eur(montant), lines, accent_color)
        cards.append(
            f'<div class="pea-card" tabindex="0" style="border-left:4px solid {accent_color};">'
            f'<div class="k">{an}</div><div class="v">{fmt_eur(montant)}</div>{tip}</div>'
        )
    st.markdown(f'<div class="pea-cards">{"".join(cards)}</div>', unsafe_allow_html=True)

def _breakdown_lines_for_kind(df_subset, kind, value_col=None):
    """Construit les lignes de détail ('Commission : xx €', ...) pour un sous-ensemble de
    transactions donné, selon le type de cartographie ('frais' ou 'dividendes')."""
    if df_subset is None or df_subset.empty:
        return []
    lines = []
    if kind == "frais":
        courtage = df_subset["Commission (€)"].fillna(0).sum() if "Commission (€)" in df_subset.columns else 0.0
        ttf = df_subset["TTF (€)"].fillna(0).sum() if "TTF (€)" in df_subset.columns else 0.0
        retenue = df_subset["Retenue_Source_Etrangere"].fillna(0).sum() if "Retenue_Source_Etrangere" in df_subset.columns else 0.0
        if courtage > 0.0001:
            lines.append(f"Commission : {fmt_eur(courtage)}")
        if ttf > 0.0001:
            lines.append(f"TTF : {fmt_eur(ttf)}")
        if retenue > 0.0001:
            lines.append(f"Retenue à la source : {fmt_eur(retenue)}")
    elif kind == "dividendes" and "Source" in df_subset.columns and value_col:
        div_amt = df_subset.loc[df_subset["Source"] == "Dividende", value_col].sum()
        rompu_amt = df_subset.loc[df_subset["Source"] == "Rompu", value_col].sum()
        if div_amt > 0.0001:
            lines.append(f"Dividende : {fmt_eur(div_amt)}")
        if rompu_amt > 0.0001:
            lines.append(f"Rompu : {fmt_eur(rompu_amt)}")
    return lines

def _fmt_cell_heat(v, zero="-"):
    """Valeur compacte écrite dans une case (les cases sont petites sur téléphone) :
    1,2k au-delà de 1000, entier de 10 à 999, sinon 1 décimale ; « - » quand la valeur est nulle.
    Le détail complet reste au survol."""
    if abs(v) < 0.05:
        return zero
    if v >= 1000:
        return f"{v / 1000:.1f}".replace(".", ",") + "k"
    if v >= 10:
        return f"{v:.0f}"
    return f"{v:.1f}".replace(".", ",")

def build_calendar_heatmap(df_source, date_col, value_col, colorscale, key_prefix, date_ouverture=None, breakdown_kind=None, unit="eur", compact=False):
    """Cartographie mensuelle : une ligne par année (la plus récente en haut), un mois par colonne,
    montant compact écrit dans chaque case, dégradé blanc -> couleur d'accent, légende horizontale
    sous le graphique. Axes numériques (0..11 / 0..n-1) avec libellés personnalisés : cases carrées-ish,
    annotations parfaitement alignées. Aucun mois futur ni antérieur à date_ouverture. Survol inchangé."""
    if df_source.empty:
        st.info("Aucune donnée à afficher pour le moment.")
        return

    if unit == "pct":
        _fmt_v = lambda x: f"{x:.2f} %".replace(".", ",")
        _cell = lambda x, zero="-": (zero if abs(x) < 0.005 else f"{x:.2f}".replace(".", ","))
        _tick = lambda x: f"{x:.2f} %".replace(".", ",")
        _lbl = "Rendement"
    else:
        _fmt_v = fmt_eur
        _cell = _fmt_cell_heat
        _tick = lambda x: _fmt_cell_heat(x, zero="0")
        _lbl = "Total"

    mois_court = ["Jan", "Fév", "Mar", "Avr", "Mai", "Jui", "Jul", "Aoû", "Sep", "Oct", "Nov", "Déc"]
    mois_hover = ["Jan", "Fév", "Mar", "Avr", "Mai", "Juin", "Juil", "Août", "Sep", "Oct", "Nov", "Déc"]

    dates = df_source[date_col]
    monthly_sum = df_source.groupby([dates.dt.year, dates.dt.month])[value_col].sum()

    today = _today_paris()
    if date_ouverture is not None and not pd.isna(date_ouverture):
        first_year = int(date_ouverture.year)
        first_month_ouverture = int(date_ouverture.month)
    else:
        first_year = int(dates.dt.year.min())
        first_month_ouverture = 1
    years = list(range(today.year, first_year - 1, -1))  # plus récente en haut (ligne 0)
    n = len(years)

    z = np.full((n, 12), np.nan)
    hover = [["" for _ in range(12)] for _ in range(n)]
    _accent = colorscale[-1] if colorscale else "#0f172a"

    for yi, year in enumerate(years):
        min_month = first_month_ouverture if year == first_year else 1
        max_month = today.month if year == today.year else 12
        for month in range(min_month, max_month + 1):
            val = float(monthly_sum.get((year, month), 0.0))
            z[yi, month - 1] = val
            cell_txt = f"<b>{mois_hover[month - 1]} {year}</b><br><span style='color:{_accent};'><b>{_lbl} : {_fmt_v(val)}</b></span>"
            if breakdown_kind is not None and val != 0:
                df_cell = df_source[(dates.dt.year == year) & (dates.dt.month == month)]
                lines = _breakdown_lines_for_kind(df_cell, breakdown_kind, value_col)
                if lines:
                    cell_txt += "<br>" + "<br>".join(lines)
            hover[yi][month - 1] = cell_txt

    zmax = float(np.nanmax(z)) if np.isfinite(z).any() else 0.0
    if zmax <= 0:
        zmax = 1.0

    annotations = []
    for yi in range(n):
        for mi in range(12):
            v = z[yi, mi]
            if np.isnan(v):
                continue
            annotations.append(dict(
                x=mi, y=yi, xref="x", yref="y", showarrow=False, text=_cell(v),
                font=dict(size=10, color="#ffffff" if (v / zmax) > 0.55 else "#0f172a"),
            ))

    row_h = 34
    plot_h = row_h * n
    top_m, bot_m = (18, 38) if (unit == "pct" or compact) else (28, 78)
    _cb_off = 6.0 if (unit == "pct" or compact) else 14.0   # écart carte -> légende (plus serré pour les rendements)
    tick_vals = [0.0, zmax / 2.0, zmax]
    tick_text = [_tick(v) for v in tick_vals]

    fig = go.Figure(data=go.Heatmap(
        z=z, x=list(range(12)), y=list(range(n)),
        text=hover, hovertemplate="%{text}<extra></extra>",
        colorscale=colorscale, zmin=0, zmax=zmax,
        xgap=2, ygap=2, hoverongaps=False, showscale=True, name="",
        colorbar=dict(
            orientation="h", x=0.5, xanchor="center",
            y=-(_cb_off / plot_h), yanchor="top", yref="paper",
            lenmode="fraction", len=0.9, thickness=10, outlinewidth=0,
            tickmode="array", tickvals=tick_vals, ticktext=tick_text,
            ticks="outside", ticklen=3, tickfont=dict(size=10),
        ),
    ))
    fig.update_layout(
        height=plot_h + top_m + bot_m,
        margin=dict(l=40, r=6, t=top_m, b=bot_m),
        annotations=annotations,
        xaxis=dict(
            showgrid=False, zeroline=False, side="top", range=[-0.5, 11.5],
            tickmode="array", tickvals=list(range(12)), ticktext=mois_court,
            tickangle=0, tickfont=dict(size=9), automargin=False,
        ),
        yaxis=dict(
            showgrid=False, zeroline=False, range=[n - 0.5, -0.5],
            tickmode="array", tickvals=list(range(n)), ticktext=[str(y) for y in years],
            tickfont=dict(size=11), automargin=False,
        ),
    )
    fig.update_layout(meta="pea-tip-top")  # infobulle posée au-dessus de la case (voir _TIP_JS)
    apply_chart_theme(fig)
    _plotly_chart(fig, use_container_width=True, theme=None, key=f"{key_prefix}_heatmap_monthly")


_ALLOC_COLORS = ["#8fb0ff", "#f2c5e8", "#c8d9ff", "#c8b8f5", "#f2b6ae", "#dda899", "#f4d9b0", "#c5dfc5", "#6fb3ad"]


def _alloc_color(i):
    if i < len(_ALLOC_COLORS):
        return _ALLOC_COLORS[i]
    return f"hsl({(i * 47) % 360}, 45%, 72%)"


def _fmt_cap(v):
    if v is None or v <= 0:
        return "N/A"
    if v >= 1e12:
        return f"{v / 1e12:,.2f} Bn€".replace(",", " ").replace(".", ",")
    if v >= 1e9:
        return f"{v / 1e9:,.1f} Md€".replace(",", " ").replace(".", ",")
    return f"{v / 1e6:,.0f} M€".replace(",", " ")

_CAP_BUCKETS = [
    ("Grandes (> 10 Md€)", 10e9, None),
    ("Moyennes (2–10 Md€)", 2e9, 10e9),
    ("Petites (300 M€–2 Md€)", 300e6, 2e9),
    ("Très petites (< 300 M€)", 0.0, 300e6),
]

def _cap_bucket(mc, qt):
    if qt in _ETF_QUOTE_TYPES:
        return "ETF / fonds"
    if mc is None or mc <= 0:
        return "Capitalisation inconnue"
    for label, lo, hi in _CAP_BUCKETS:
        if mc >= lo and (hi is None or mc < hi):
            return label
    return "Capitalisation inconnue"


_ALLOC4_HTML = r"""
<style>
  @import url('https://fonts.googleapis.com/css2?family=Manrope:wght@500;700;800&display=swap');
  html, body { margin: 0; padding: 0; background: transparent; }
  #root { box-sizing: border-box; padding: 4px 2px; font-family: Manrope, Inter, system-ui, -apple-system, 'Segoe UI', sans-serif;
          color: var(--fg, #334155); }
  #grid { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 14px 10px; align-items: start; }
  .cell { min-width: 0; }
  .ttl { text-align: center; font-size: 11px; font-weight: 700; letter-spacing: .04em; text-transform: uppercase; opacity: .6; margin-bottom: 2px; }
  svg { width: 100%; max-width: 196px; height: auto; display: block; margin: 0 auto; -webkit-tap-highlight-color: transparent; }
  .slice { cursor: pointer; transition: opacity .18s ease, transform .18s ease; }
  .slice.dim { opacity: .28; }
  .leg { margin-top: 4px; }
  .row { display: flex; align-items: center; gap: 8px; padding: 4px 6px; border-radius: 8px; cursor: pointer;
         transition: opacity .18s ease, background .18s ease; -webkit-tap-highlight-color: transparent; }
  .row.sel { background: rgba(127,127,127,.14); }
  .row.dim { opacity: .4; }
  .dot { width: 10px; height: 10px; border-radius: 3px; flex: 0 0 10px; }
  .nm { flex: 1; min-width: 0; font-size: 12.5px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .pc { font-weight: 700; font-variant-numeric: tabular-nums; font-size: 12px; opacity: .85; }
  text { font-family: inherit; fill: var(--fg, #334155); pointer-events: none; }
  html, body, svg, .row { -webkit-user-select: none; user-select: none; -webkit-touch-callout: none; }
  .mono { font-variant-numeric: tabular-nums; letter-spacing: -0.03em; }
  /* Téléphone : 2 x 2 serrés, légende toujours visible sous chaque camembert, lignes compactes pour que
     l'ensemble tienne si possible sur un seul écran ; une seule ligne d'écart entre les deux rangées. */
  @media (max-width: 760px) {
    #grid { grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 14px 6px; }
    .ttl { font-size: 10px; margin-bottom: 0; }
    .leg { margin-top: 0; }
    .nm { font-size: 11px; } .pc { font-size: 10.5px; }
    .row { padding: 1px 3px; gap: 5px; }
    .dot { width: 8px; height: 8px; flex: 0 0 8px; border-radius: 2px; }
  }
</style>
<div id="root">
  <div id="grid"></div>
</div>
<script>
(function () {
  var DON = __DON__;
  var fg = '#334155';
  try { fg = window.parent.getComputedStyle(window.parent.document.body).color || fg; } catch (e) {}
  document.documentElement.style.setProperty('--fg', fg);

  var NS = 'http://www.w3.org/2000/svg', C = 120, RAD = 106, r = 78, mute = 0;
  var st = { t: -1, i: -1 };
  var grid = document.getElementById('grid'), rootEl = document.getElementById('root');

  function layoutP(p) {
    var MIN = 2.2, raw = p.map(function (x) { return x > 0.0001 ? Math.max(x * 3.6, MIN) : 0; });
    var sum = raw.reduce(function (a, b) { return a + b; }, 0) || 1, k = 360 / sum, ang = [], a0 = 0;
    raw.forEach(function (v) { var a = v * k; ang.push([a0, a0 + a]); a0 += a; });
    return ang;
  }
  function f2(x) { return x.toFixed(2).replace('.', ','); }
  function pt(rad, a) { var t = (a - 90) * Math.PI / 180; return [C + rad * Math.cos(t), C + rad * Math.sin(t)]; }
  function arc(s, e) {
    var gap = (e - s) > 4 ? 0.5 : 0.15; s += gap; e -= gap;
    if (e - s >= 359.9) e = s + 359.9;
    var big = (e - s) > 180 ? 1 : 0, p0 = pt(RAD, s), p1 = pt(RAD, e), p2 = pt(r, e), p3 = pt(r, s);
    return 'M' + p0 + 'A' + RAD + ',' + RAD + ' 0 ' + big + ' 1 ' + p1 + 'L' + p2 + 'A' + r + ',' + r + ' 0 ' + big + ' 0 ' + p3 + 'Z';
  }
  function el(n, at, parent) {
    var e = document.createElementNS(NS, n);
    for (var key in at) e.setAttribute(key, at[key]);
    parent.appendChild(e); return e;
  }
  function cut(s, n) { return s.length > n ? s.slice(0, n - 1) + '…' : s; }
  function plural(n, w) { return n + ' ' + (n > 1 ? w[1] : w[0]); }
  function inter(a, b) { for (var i = 0; i < a.length; i++) if (b.indexOf(a[i]) >= 0) return true; return false; }

  function toggle(t, i) {
    if (st.t === t && st.i === i) st = { t: -1, i: -1 }; else st = { t: t, i: i };
    render();
  }

  DON.forEach(function (D, t) {
    D.ang = layoutP(D.items.map(function (d) { return d.pct; }));
    var cell = document.createElement('div'); cell.className = 'cell';
    cell.innerHTML = '<div class="ttl"></div><svg viewBox="0 0 240 240"></svg><div class="leg"></div>';
    cell.querySelector('.ttl').textContent = D.title;
    grid.appendChild(cell);
    var svg = cell.querySelector('svg'), leg = cell.querySelector('.leg');
    D.sl = D.items.map(function (d, i) {
      var p = el('path', { d: arc(D.ang[i][0], D.ang[i][1]), fill: d.c, 'class': 'slice', 'data-t': t, 'data-i': i }, svg);
      p.addEventListener('click', function (ev) { ev.stopPropagation(); if (Date.now() < mute) return; toggle(t, i); });
      return p;
    });
    D.ct = [
      el('text', { x: C, y: C - 26, 'text-anchor': 'middle', 'font-size': 12, opacity: .7 }, svg),
      el('text', { x: C, y: C - 2, 'text-anchor': 'middle', 'font-size': 18, 'font-weight': 700, 'class': 'mono' }, svg),
      el('text', { x: C, y: C + 17, 'text-anchor': 'middle', 'font-size': 12, opacity: .7 }, svg),
      el('text', { x: C, y: C + 34, 'text-anchor': 'middle', 'font-size': 11, opacity: .7 }, svg)
    ];
    D.rows = D.items.map(function (d, i) {
      var row = document.createElement('div'); row.className = 'row'; row.setAttribute('data-t', t); row.setAttribute('data-i', i);
      row.innerHTML = '<span class="dot" style="background:' + d.c + '"></span><span class="nm"></span><span class="pc">' + d.pt + ' %</span>';
      row.querySelector('.nm').textContent = d.n; row.title = d.n + ' — ' + d.v;
      row.addEventListener('click', function (ev) { ev.stopPropagation(); if (Date.now() < mute) return; toggle(t, i); });
      leg.appendChild(row); return row;
    });
  });

  function paint(D, isAct, on) {
    D.sl.forEach(function (s, j) {
      var a = on && isAct(j);
      s.setAttribute('class', 'slice' + (on && !a ? ' dim' : ''));
      if (a) {
        var m = (D.ang[j][0] + D.ang[j][1]) / 2 * Math.PI / 180;
        s.style.transform = 'translate(' + (Math.sin(m) * 5) + 'px,' + (-Math.cos(m) * 5) + 'px)';
      } else { s.style.transform = ''; }
    });
    D.rows.forEach(function (rw, j) {
      var a = on && isAct(j);
      rw.className = 'row' + (a ? ' sel' : '') + (on && !a ? ' dim' : '');
    });
  }
  function txt(c, a, b, d, e) { c[0].textContent = a; c[1].textContent = b; c[2].textContent = d; c[3].textContent = e; }
  function show(D, d) { txt(D.ct, cut(d.n, 20), d.v, d.pt + ' %', d.x ? cut(d.x, 22) : plural(d.m.length, DON[0].nouns)); }

  // Redessine un anneau à partir de pourcentages (0 = part masquée, y compris dans la légende).
  function setGeom(D, pcts, base) {
    D.ang = layoutP(pcts);
    D.sl.forEach(function (sl, j) {
      sl.setAttribute('d', pcts[j] > 0.0001 ? arc(D.ang[j][0], D.ang[j][1]) : '');
    });
    D.rows.forEach(function (rw, j) {
      rw.style.display = pcts[j] > 0.0001 ? '' : 'none';
      rw.querySelector('.pc').textContent = (base ? D.items[j].pt : f2(pcts[j])) + ' %';
    });
  }

  // Sélection d'une part (camembert t0, part i0) : « poids effectif » de chaque action dans cette part, puis les trois
  // autres camemberts sont recalculés sur ce seul sous-ensemble (répartition DE la sélection, base 100 %).
  //  - Vusion cliqué  -> continents = répartition du chiffre d'affaires de Vusion ; secteur / tranche = les siens.
  //  - Technologie cliqué -> actions = poids relatif des valeurs technologiques ; continents = leur CA cumulé.
  function render() {
    var on = st.t >= 0, W = DON[0].W;
    var sel = on ? DON[st.t].items[st.i] : null, eff = [], tot = 0;
    if (on) {
      DON[st.t].f.forEach(function (fr, h) {
        var q = 0; fr.forEach(function (p) { if (p[0] === st.i) q = p[1]; });
        eff[h] = W[h] * q; tot += eff[h];
      });
    }
    DON.forEach(function (D, t) {
      if (!on || t === st.t) {
        setGeom(D, D.items.map(function (d) { return d.pct; }), true);
        paint(D, function (j) { return on && j === st.i; }, on);
        if (!on) txt(D.ct, D.rest[0], D.rest[1], D.rest[2], D.rest[3]); else show(D, sel);
        return;
      }
      var vals = D.items.map(function () { return 0; });
      D.f.forEach(function (fr, h) { if (eff[h]) fr.forEach(function (p) { vals[p[0]] += eff[h] * p[1]; }); });
      setGeom(D, vals.map(function (v) { return tot > 0 ? v / tot * 100 : 0; }), false);
      paint(D, function () { return false; }, false);
      txt(D.ct, 'Répartition de', cut(sel.n, 16), sel.v, sel.pt + ' % du portefeuille');
    });
  }
  document.body.addEventListener('click', function () { if (Date.now() < mute) return; if (st.t >= 0) { st = { t: -1, i: -1 }; render(); } });
  document.addEventListener('contextmenu', function (e) { e.preventDefault(); });

  // Doigt maintenu (~0,25 s) sur une part ou une ligne de légende, puis glissé : la sélection suit le doigt.
  var timer = null, scrub = false, sx = 0, sy = 0;
  function hitAt(x, y) {
    var e = document.elementFromPoint(x, y);
    while (e && e !== document.body) {
      var v = e.getAttribute && e.getAttribute('data-i');
      if (v !== null && v !== undefined) return { t: +e.getAttribute('data-t'), i: +v };
      e = e.parentNode;
    }
    return null;
  }
  function stopHold() { if (timer) { clearTimeout(timer); timer = null; } if (scrub) { scrub = false; mute = Date.now() + 450; } }
  document.addEventListener('touchstart', function (e) {
    stopHold();
    if (e.touches.length !== 1) return;
    sx = e.touches[0].clientX; sy = e.touches[0].clientY;
    if (!hitAt(sx, sy)) return;
    timer = setTimeout(function () {
      timer = null; scrub = true;
      if (navigator.vibrate) { try { navigator.vibrate(8); } catch (_) {} }
      var h = hitAt(sx, sy); if (h) { st = h; render(); }
    }, 250);
  }, { passive: true });
  document.addEventListener('touchmove', function (e) {
    var t = e.touches[0];
    if (scrub) {
      e.preventDefault();
      var h = hitAt(t.clientX, t.clientY);
      if (h && (h.t !== st.t || h.i !== st.i)) { st = h; render(); }
    } else if (timer && (Math.abs(t.clientX - sx) > 10 || Math.abs(t.clientY - sy) > 10)) {
      clearTimeout(timer); timer = null;
    }
  }, { passive: false });
  document.addEventListener('touchend', stopHold, { passive: true });
  document.addEventListener('touchcancel', stopHold, { passive: true });

  function fit() {
    try {
      var h = Math.ceil(rootEl.getBoundingClientRect().height) + 16;
      try {
        var fe = window.frameElement;
        fe.style.height = h + 'px'; fe.setAttribute('height', h);
        // Streamlit fixe aussi la hauteur du conteneur parent : on l'aligne, sinon la section suivante chevauche la légende
        // (cadre trop court) ou laisse un grand vide (cadre trop haut).
        var p = fe.parentElement, k = 0;
        while (p && k < 4) {
          var cls = String(p.className || '');
          if ((p.style && p.style.height) || /stElementContainer|element-container/.test(cls)) { p.style.height = h + 'px'; }
          if (/stElementContainer|element-container/.test(cls)) break;
          p = p.parentElement; k++;
        }
      }
      catch (e2) { window.parent.postMessage({ isStreamlitMessage: true, type: 'streamlit:setFrameHeight', height: h }, '*'); }
    } catch (e) {}
  }
  render(); fit();
  window.addEventListener('resize', fit); setTimeout(fit, 150); setTimeout(fit, 600); setTimeout(fit, 1500);
  try { new ResizeObserver(fit).observe(rootEl); } catch (e) {}
  try { document.fonts.ready.then(fit); } catch (e) {}
})();
</script>
"""

def _render_allocation(df_active, cash):
    """Deux camemberts (anneaux) liés : par ACTION et par TRANCHE DE CAPITALISATION (Yahoo). Composant 100 % côté navigateur (aucun rechargement au clic). Au repos le centre affiche
    un total ; au clic sur une part (ou sa ligne de légende), l'autre camembert est recalculé sur cette seule sélection
    (base 100 %). Un second clic (ou un clic à côté) désélectionne."""
    import streamlit.components.v1 as components
    rows = []
    if df_active is not None and not df_active.empty:
        for _, r in df_active.iterrows():
            v = float(r["Valeur Actuelle (€)"])
            if v > 0:
                rows.append((str(r["Nom"]), str(r["Ticker"]), v, "", None))
    if not rows:
        st.info("Aucune position à répartir pour le moment.")
        return
    rows.sort(key=lambda x: -x[2])
    total = sum(x[2] for x in rows)
    _pct = lambda p: f"{p:.2f}".replace(".", ",")

    def _groupe(cles, offset=0, ordre=None, extra=None):
        val, mem = {}, {}
        for idx, k in enumerate(cles):
            val[k] = val.get(k, 0.0) + rows[idx][2]
            mem.setdefault(k, []).append(idx)
        ordre = [k for k in (ordre or sorted(val, key=lambda k: -val[k])) if k in val]
        return [{"n": k, "v": fmt_eur(val[k]), "pct": val[k] / total * 100, "pt": _pct(val[k] / total * 100),
                 "c": _alloc_color(i + offset), "m": mem[k]} for i, k in enumerate(ordre)]

    # Tranche de capitalisation de chaque action (Yahoo : capitalisation de marché ; les ETF forment leur propre part)
    caps, cap_total, n_cap = [], 0.0, 0
    for (_n, tick, _v, _s, _p) in rows:
        mc, qt, _cur = get_ticker_marketcap(tick)
        caps.append(_cap_bucket(mc, qt))
        if mc and qt not in _ETF_QUOTE_TYPES:
            cap_total += float(mc)
            n_cap += 1
    # 1) Actions (une part par position ; le 4e texte du centre = la tranche de capitalisation)
    A = [{"n": n, "v": fmt_eur(v), "pct": v / total * 100, "pt": _pct(v / total * 100),
          "c": _alloc_color(i), "m": [i], "x": caps[i]} for i, (n, _t, v, _sc, _p) in enumerate(rows)]
    # 2) Tranches de capitalisation
    K = _groupe(caps, offset=3, ordre=[b[0] for b in _CAP_BUCKETS] + ["ETF / fonds", "Capitalisation inconnue"])

    # Fraction de chaque action (ligne) rattachée à chaque part : sert au recalcul croisé côté navigateur.
    _iK = {it["n"]: i for i, it in enumerate(K)}
    A_f = [[[i, 1.0]] for i in range(len(rows))]
    K_f = [[[_iK[c], 1.0]] for c in caps]

    plur = lambda n, a, b: f"{n} {a if n < 2 else b}"
    don = [
        {"title": "Par action", "items": A, "nouns": ["action", "actions"],
         "rest": ["Total portefeuille", fmt_eur(total), plur(len(A), "position", "positions"), ""]},
        {"title": "Par capitalisation", "items": K, "nouns": ["tranche", "tranches"],
         "rest": ["Capitalisation cumulée", _fmt_cap(cap_total) if n_cap else "N/A", plur(n_cap, "société", "sociétés"), "(hors ETF)"]},
    ]
    for _d, _f in zip(don, (A_f, K_f)):
        _d["f"] = _f
    don[0]["W"] = [x[2] / total for x in rows]
    payload = json.dumps(don, ensure_ascii=False).replace("</", "<\\/")
    page = _ALLOC4_HTML.replace("__DON__", payload)
    # Un seul rang de deux camemberts : hauteur = titre + anneau (~196 px) + une ligne de légende par part.
    components.html(page, height=int(205 + max(len(A), len(K)) * 16.5 + 14))


def _progress_bar_html(pct, gradient, glow_color, texte):
    """Barre de progression pleine largeur (objectif, net conservé après retrait)."""
    pct_c = max(0.0, min(float(pct), 100.0))
    return (
        '<div style="background:#e2e8f0; border-radius:999px; height:34px; overflow:hidden; position:relative; box-shadow: inset 0 2px 5px rgba(0,0,0,0.10);">'
        f'<div style="width:{pct_c}%; height:100%; background:{gradient}; border-radius:999px; transition:width 0.6s ease-in-out; position:relative; box-shadow: 0 0 14px {glow_color}66;">'
        '<div style="position:absolute; inset:0; border-radius:999px; background:linear-gradient(180deg, rgba(255,255,255,0.40) 0%, rgba(255,255,255,0.05) 45%, rgba(255,255,255,0) 60%);"></div></div>'
        '<div style="position:absolute; inset:0; display:flex; align-items:center; justify-content:center; padding:0 8px; text-align:center; '
        f'font-size:0.88rem; font-weight:800; color:#0f172a; text-shadow: 0 1px 3px rgba(255,255,255,0.75);">{texte}</div></div>'
    )


_JAUGE_HTML = r"""
<style>
  html, body { margin: 0; padding: 0; background: transparent; }
  #w { position: relative; max-width: 380px; margin: 0 auto; font-family: Manrope, Inter, system-ui, sans-serif; color: var(--fg, #334155);
       -webkit-tap-highlight-color: transparent; user-select: none; -webkit-user-select: none; cursor: pointer; }
  svg { width: 100%; height: auto; display: block; }
  text { font-family: inherit; fill: var(--fg, #334155); pointer-events: none; }
  #tip { position: absolute; display: none; padding: 7px 12px; border-radius: 10px; font-size: 13px; font-weight: 700; line-height: 1.35;
         text-align: center; white-space: nowrap; box-shadow: 0 6px 18px rgba(0,0,0,.25); transform: translate(-50%, -125%); pointer-events: none; }
  #tip small { display: block; font-weight: 600; opacity: .9; font-size: 11.5px; }
</style>
<div id="w"><svg id="g" viewBox="0 0 300 190"></svg><div id="tip"></div></div>
<script>
(function () {
  var D = __DATA__;
  var fg = '#334155';
  try { fg = window.parent.getComputedStyle(window.parent.document.body).color || fg; } catch (e) {}
  document.documentElement.style.setProperty('--fg', fg);
  var NS = 'http://www.w3.org/2000/svg', CX = 150, CY = 150, R = 112, SW = 22;
  // Palette logique selon la position sur la jauge : vert (large marge) -> lime -> ambre -> orange -> rouge (plafond proche).
  var STOPS = [[0, [22,163,74]], [45, [132,204,22]], [70, [245,158,11]], [88, [249,115,22]], [100, [220,38,38]]];
  function colorAt(p) {
    p = Math.max(0, Math.min(100, p));
    for (var i = 1; i < STOPS.length; i++) {
      if (p <= STOPS[i][0]) {
        var a = STOPS[i-1], b = STOPS[i], t = (p - a[0]) / (b[0] - a[0]);
        return [0,1,2].map(function (k) { return Math.round(a[1][k] + (b[1][k] - a[1][k]) * t); });
      }
    }
    return STOPS[STOPS.length-1][1];
  }
  function rgb(c, a) { return 'rgba(' + c[0] + ',' + c[1] + ',' + c[2] + ',' + (a === undefined ? 1 : a) + ')'; }
  function pt(f, r) { var th = Math.PI * f; return [CX - r * Math.cos(th), CY - r * Math.sin(th)]; }
  var svg = document.getElementById('g');
  function el(n, at) { var e = document.createElementNS(NS, n); for (var k in at) e.setAttribute(k, at[k]); svg.appendChild(e); return e; }
  var pct = Math.max(0, Math.min(100, D.pct)), N = 100;
  for (var i = 0; i < N; i++) {
    var f0 = i / N, f1 = (i + 1) / N + 0.0015, p0 = pt(f0, R), p1 = pt(f1, R);
    var on = (i + 0.5) < pct;
    el('path', { d: 'M' + p0 + 'A' + R + ',' + R + ' 0 0 1 ' + p1, fill: 'none', 'stroke-width': SW, stroke: rgb(colorAt(i + 0.5), on ? 1 : 0.2) });
  }
  var cur = colorAt(pct), fm = pct / 100, pm = pt(fm, R);
  // repères 0 / 50 k / 100 k / 150 k
  [[0, '0'], [1/3, D.t1], [2/3, D.t2], [1, D.t3]].forEach(function (t) {
    var p = pt(t[0], R + 24);
    var x = p[0], y = p[1] + (t[0] === 0 || t[0] === 1 ? 14 : 4);
    var tx = el('text', { x: x, y: y, 'text-anchor': 'middle', 'font-size': 10.5, opacity: .7 }); tx.textContent = t[1];
  });
  var mk = el('circle', { cx: pm[0], cy: pm[1], r: 8.5, fill: rgb(cur), stroke: '#ffffff', 'stroke-width': 3 });
  var c1 = el('text', { x: CX, y: CY - 6, 'text-anchor': 'middle', 'font-size': 30, 'font-weight': 800 }); c1.textContent = D.pct_txt;
  c1.style.fill = rgb(cur);
  var c2 = el('text', { x: CX, y: CY + 16, 'text-anchor': 'middle', 'font-size': 11.5, opacity: .7 }); c2.textContent = 'du plafond';
  var tip = document.getElementById('tip'), w = document.getElementById('w');
  var lum = (0.299 * cur[0] + 0.587 * cur[1] + 0.114 * cur[2]) / 255;
  tip.style.background = rgb(cur); tip.style.color = lum > 0.62 ? '#1f2937' : '#ffffff';
  tip.innerHTML = D.amount + '<small>' + D.pct_txt + ' du plafond</small>';
  function place() {
    var box = svg.getBoundingClientRect(), k = box.width / 300, tw = tip.offsetWidth;
    var x = Math.min(Math.max(pm[0] * k, tw / 2 + 4), box.width - tw / 2 - 4), y = pm[1] * k;
    tip.style.left = x + 'px';
    if (y < 70) { tip.style.transform = 'translate(-50%, 35%)'; tip.style.top = y + 'px'; }
    else { tip.style.transform = 'translate(-50%, -125%)'; tip.style.top = (y - 12) + 'px'; }
  }
  var open = false;
  function setOpen(v) { open = v; tip.style.display = v ? 'block' : 'none'; if (v) place(); fit(); }
  w.addEventListener('click', function (e) { e.stopPropagation(); setOpen(!open); });
  document.body.addEventListener('click', function () { if (open) setOpen(false); });
  function fit() {
    try {
      var h = Math.ceil(w.getBoundingClientRect().height) + 14;
      try { window.frameElement.style.height = h + 'px'; }
      catch (e2) { window.parent.postMessage({ isStreamlitMessage: true, type: 'streamlit:setFrameHeight', height: h }, '*'); }
    } catch (e) {}
  }
  window.addEventListener('resize', function () { if (open) place(); fit(); });
  fit(); setTimeout(fit, 150);
})();
</script>
"""

def _render_jauge_pea(total_verse, plafond):
    """Jauge semi-circulaire des versements cumulés sur le plafond du PEA : palette vert -> rouge selon la position,
    et au clic une infobulle (montant versé) dans la couleur de la jauge à l'endroit atteint."""
    import streamlit.components.v1 as components
    pct = (total_verse / plafond * 100.0) if plafond > 0 else 0.0
    reste = max(plafond - total_verse, 0.0)
    pct_txt = f"{pct:.1f} %".replace(".", ",")
    data = {
        "pct": pct, "pct_txt": pct_txt, "amount": fmt_eur(total_verse),
        "t1": f"{plafond / 3 / 1000:.0f} k€", "t2": f"{plafond * 2 / 3 / 1000:.0f} k€", "t3": f"{plafond / 1000:.0f} k€",
        "sub": f"{_esc(fmt_eur(total_verse))} versés sur {_esc(fmt_eur(plafond))} · reste <b>{_esc(fmt_eur(reste))}</b>",
    }
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    components.html(_JAUGE_HTML.replace("__DATA__", payload), height=250)


_FAILED_TICKERS = set()  # se remplit automatiquement avec les tickers dont le cours est introuvable

@st.cache_data(ttl=600, show_spinner=False)
def _get_live_price_real(ticker):
    if not ticker or ticker in _FAILED_TICKERS:
        return None
    try:
        t = yf.Ticker(ticker)
        # fast_info["last_price"] reflète le dernier cours réellement coté (quasi temps réel),
        # contrairement à history()["Close"] qui renvoie la clôture de la bougie journalière —
        # laquelle peut ne pas être à jour en cours de séance, ou accuser un décalage d'un jour
        # selon le moment où Yahoo Finance finalise la bougie du jour. C'est cette dernière
        # source (moins fiable en intraday) qui explique l'écart constaté avec le courtier.
        try:
            last_p = t.fast_info["last_price"]
            if last_p is not None and not np.isnan(last_p) and last_p > 0:
                return last_p
        except Exception:
            pass
        hist = t.history(period="5d", auto_adjust=True)
        if not hist.empty:
            return hist["Close"].dropna().iloc[-1]
        _FAILED_TICKERS.add(ticker)
        return None
    except Exception:
        _FAILED_TICKERS.add(ticker)
        return None

@st.cache_data(ttl=600, show_spinner=False)
def get_previous_close(ticker):
    """Clôture de la séance précédente donnée par Yahoo (fast_info). Sert uniquement à combler la clôture de la
    veille quand la bougie journalière correspondante manque dans l'historique."""
    if not ticker or ticker in _FAILED_TICKERS:
        return None
    try:
        v = yf.Ticker(ticker).fast_info["previous_close"]
        return float(v) if v is not None and not np.isnan(v) and v > 0 else None
    except Exception:
        return None


# Le secteur et le pays d'une valeur ne changent pratiquement jamais, mais la requête qui les
# donne (t.info) est la plus lourde de Yahoo Finance, et elle était refaite pour CHAQUE ticker
# (y compris les positions soldées depuis des années) à chaque redémarrage de l'application :
# c'est environ un tiers des requêtes du préchargement au démarrage. On les mémorise donc dans
# un petit fichier JSON à côté de transactions.csv, valables 30 jours. Seuls les résultats
# COMPLETS sont écrits : un échec réseau ou une réponse vide de Yahoo (limitation de débit) ne
# sont jamais conservés, comme avant où ils ne restaient en cache que 24 h en mémoire.
# Le bouton « Rafraîchir toutes les données » vide aussi ce fichier.
_TICKER_INFO_FILE = "ticker_info_cache.json"
_TICKER_INFO_MAX_AGE = 30 * 86400  # secondes

class _TickerInfoStore:
    def __init__(self, path):
        import threading as _threading
        self.path = path
        self.lock = _threading.Lock()
        self.data = {}
        try:
            with open(path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                self.data = loaded
        except Exception:
            self.data = {}

    def lookup(self, ticker):
        """Renvoie le dict mémorisé (sector, country, mc, qt, cur) s'il est frais ET complet, sinon None.
        Les anciennes entrées (sans « qt » = type de produit) ou celles dont le secteur vaut « Autre » sans
        être un ETF sont ignorées : elles proviennent d'une réponse Yahoo incomplète (limitation de débit)
        et étaient la cause de l'affichage « tout en Autre » dans la répartition par secteur."""
        entry = self.data.get(ticker)
        try:
            if entry and (time_module.time() - float(entry.get("ts", 0))) < _TICKER_INFO_MAX_AGE and "qt" in entry:
                return entry
        except Exception:
            pass
        return None

    def save(self, ticker, entry):
        with self.lock:
            self.data[ticker] = dict(entry, ts=time_module.time())
            try:
                tmp_path = self.path + ".tmp"
                with open(tmp_path, "w", encoding="utf-8") as f:
                    json.dump(self.data, f, ensure_ascii=False)
                os.replace(tmp_path, self.path)
            except Exception:
                pass  # écriture impossible : on continue simplement sans mémorisation disque

    def clear(self):
        with self.lock:
            self.data = {}
            try:
                if os.path.exists(self.path):
                    os.remove(self.path)
            except Exception:
                pass

@st.cache_resource(show_spinner=False)
def _ticker_info_store():
    return _TickerInfoStore(_TICKER_INFO_FILE)

import threading as _threading_info
# Au plus 4 requêtes « info » simultanées vers Yahoo : le préchargement lance ~20 threads en parallèle,
# ce qui déclenchait la limitation de débit (réponse vide) -> secteur « Autre » pour toutes les valeurs.
_INFO_SEMAPHORE = _threading_info.Semaphore(4)
_ETF_QUOTE_TYPES = ("ETF", "MUTUALFUND", "INDEX")

@st.cache_resource(show_spinner=False)
def _info_fail_registry():
    return {}

@st.cache_data(ttl=86400, show_spinner=False)
def _fetch_info_full(ticker):
    """Secteur, pays, capitalisation boursière et type de produit d'une valeur (une seule requête Yahoo).
    LÈVE une exception si Yahoo ne répond pas correctement : st.cache_data ne mémorise jamais une
    exception, donc un échec passager n'est plus figé pendant 24 h (c'était la cause du « tout en Autre »)."""
    _known = _ticker_info_store().lookup(ticker)
    if _known is not None:
        return {k: _known.get(k) for k in ("sector", "country", "mc", "qt", "cur")}
    _reg = _info_fail_registry()
    if time_module.time() - _reg.get(ticker, 0.0) < 600:
        raise RuntimeError(f"info indisponible pour {ticker} (nouvel essai dans quelques minutes)")
    info = None
    last_exc = None
    for attempt in range(3):
        try:
            with _INFO_SEMAPHORE:
                info = yf.Ticker(ticker).info
            if isinstance(info, dict) and len(info) >= 5:
                break
            info = None
        except Exception as exc:
            last_exc = exc
            info = None
        time_module.sleep(0.8 * (attempt + 1))
    if info is None:
        _reg[ticker] = time_module.time()
        raise RuntimeError(f"info indisponible pour {ticker}: {last_exc}")
    _reg.pop(ticker, None)
    qt = str(info.get("quoteType") or "").upper()
    sector = info.get("sector") or ("ETF / Fonds" if qt in _ETF_QUOTE_TYPES else "Autre")
    out = {
        "sector": sector,
        "country": info.get("country") or "Inconnu",
        "mc": info.get("marketCap"),
        "qt": qt or "EQUITY",
        "cur": info.get("currency"),
    }
    # On n'écrit sur disque que les réponses réellement complètes (secteur connu, ou ETF).
    if info.get("sector") or qt in _ETF_QUOTE_TYPES:
        _ticker_info_store().save(ticker, out)
    return out

@st.cache_data(ttl=3600, show_spinner=False)
def _fetch_info_fallback(ticker):
    """Repli quand la page « info » de Yahoo ne répond pas : type de produit, devise et capitalisation via d'autres
    points d'accès (fast_info / métadonnées de l'historique de cours)."""
    mc = qt = cur = None
    tk = yf.Ticker(ticker)
    try:
        fi = tk.fast_info
        try:
            v = float(fi["market_cap"])
            mc = v if v > 0 else None
        except Exception:
            mc = None
        try:
            cur = fi["currency"]
        except Exception:
            cur = None
    except Exception:
        pass
    try:
        md = tk.history_metadata or {}
        qt = str(md.get("instrumentType") or "").upper() or None
        cur = cur or md.get("currency")
    except Exception:
        pass
    return {"mc": mc, "qt": qt or "", "cur": cur}

def _info_fallback_safe(ticker):
    try:
        return _fetch_info_fallback(ticker)
    except Exception:
        return {"mc": None, "qt": "", "cur": None}


def get_ticker_marketcap(ticker):
    """(capitalisation en €, type de produit, devise) ; capitalisation None pour un ETF / si inconnue."""
    if not ticker or ticker in _FAILED_TICKERS:
        return None, "", None
    try:
        d = _fetch_info_full(ticker)
        return d.get("mc"), d.get("qt") or "", d.get("cur")
    except Exception:
        fb = _info_fallback_safe(ticker)
        return fb.get("mc"), fb.get("qt") or "", fb.get("cur")

@st.cache_data(ttl=3600, show_spinner=False)
def get_historical_price_at(ticker, target_date):
    if not ticker or ticker in _FAILED_TICKERS:
        return None
    try:
        start_d = (target_date - pd.Timedelta(days=7)).strftime("%Y-%m-%d")
        end_d = (target_date + pd.Timedelta(days=1)).strftime("%Y-%m-%d")
        hist = yf.Ticker(ticker).history(start=start_d, end=end_d, auto_adjust=True)
        if hist.empty:
            return None
        hist_filtered = hist[hist.index.date <= target_date.date()]
        if not hist_filtered.empty:
            return hist_filtered["Close"].dropna().iloc[-1]
        return hist["Close"].dropna().iloc[0]
    except Exception:
        return None

@st.cache_data(ttl=1800, show_spinner=False)
def _get_ticker_history_real(ticker, start_date_str):
    """Historique complet des clôtures d'un ticker depuis start_date_str, mis en cache 30 min
    (au lieu de 5 min : le passé ne change pas, et le dernier point est de toute façon remplacé
    par le cours en direct, lui rafraîchi toutes les 10 min, dans get_portfolio_history_cached).
    Isolée dans sa propre fonction cachée pour pouvoir être préchargée EN MÊME TEMPS que
    get_live_price dans _prefetch_market_data, au lieu d'une deuxième vague
    de requêtes réseau séquentielle lancée plus tard par get_portfolio_history_cached (c'était
    la principale cause de lenteur au premier chargement : deux allers-retours Yahoo Finance
    l'un après l'autre au lieu d'un seul en parallèle)."""
    if not ticker or ticker in _FAILED_TICKERS:
        return pd.DataFrame()
    try:
        return yf.Ticker(ticker).history(start=start_date_str, auto_adjust=True)
    except Exception:
        return pd.DataFrame()

# ------------------------------------------------------------------
# AFFICHAGE IMMÉDIAT PUIS ACTUALISATION EN ARRIÈRE-PLAN (« stale-while-revalidate »)
# Ouvrir le dashboard avec des caches de cours vides (redémarrage, ou cours expirés) obligeait à
# attendre ~10 s de requêtes Yahoo Finance avant de voir le moindre chiffre. Désormais, après
# chaque actualisation complète, les derniers cours (cours en direct + historiques) sont
# enregistrés dans market_snapshot.pkl. À l'ouverture suivante, si les caches sont froids, la
# page s'affiche tout de suite à partir de ces derniers cours connus, avec un bandeau
# « actualisation en cours », pendant qu'un thread récupère les cours frais en arrière-plan ;
# quand il a fini, la page se relance toute seule avec les chiffres à jour. La toute première
# ouverture (aucun instantané) et le bouton « Rafraîchir toutes les données » gardent l'attente
# habituelle : on n'affiche jamais de chiffres périmés sur demande explicite de rafraîchissement.
# Mettre _SWR_ENABLED_SETTING à False pour revenir à l'attente au démarrage.
# ------------------------------------------------------------------
_SWR_ENABLED_SETTING = True
_MARKET_SNAPSHOT_FILE = "market_snapshot.pkl"
_MARKET_SNAPSHOT_MAX_AGE = 5 * 86400    # au-delà (ex. après des vacances), l'instantané est ignoré : attente classique plutôt que des chiffres trop anciens
_MARKET_FRESH_WINDOW = 600              # s : en deçà de la dernière actualisation complète, les caches sont chauds
_SWR_REFRESH_TIMEOUT = 120              # s : durée maximale de l'actualisation en arrière-plan
try:
    import inspect as _inspect_swr
    _SWR_ENABLED = bool(_SWR_ENABLED_SETTING) and hasattr(st, "fragment") and ("run_every" in _inspect_swr.signature(st.fragment).parameters)
except Exception:
    _SWR_ENABLED = False

class _MarketSWR:
    """État partagé par tout le processus Streamlit (via st.cache_resource)."""
    def __init__(self, path):
        import threading as _threading
        self._threading = _threading
        self.path = path
        self.lock = _threading.Lock()
        self.serve_stale = False      # True tant que la page s'appuie sur l'instantané
        self.refreshing = False
        self.last_fresh_ts = 0.0      # dernière actualisation complète des caches réseau
        self.epoch = 0                # +1 à chaque fin d'actualisation en arrière-plan
        self.force_blocking = False   # « Rafraîchir toutes les données » : attente classique
        self.snapshot = None
        self.last_error = None
        self._load()

    def _load(self):
        import pickle
        try:
            with open(self.path, "rb") as f:
                snap = pickle.load(f)
            if (isinstance(snap, dict) and isinstance(snap.get("live"), dict) and isinstance(snap.get("hist"), dict)
                    and (time_module.time() - float(snap.get("ts", 0))) < _MARKET_SNAPSHOT_MAX_AGE):
                self.snapshot = snap
        except Exception:
            self.snapshot = None

    def can_serve_stale(self):
        if self.serve_stale:
            return True
        return (self.snapshot is not None and not self.force_blocking
                and (time_module.time() - self.last_fresh_ts) > _MARKET_FRESH_WINDOW)

    def snapshot_live(self, ticker):
        snap = self.snapshot
        if snap is not None and ticker in snap["live"]:
            return True, snap["live"][ticker]
        return False, None

    def snapshot_hist(self, ticker, start_date_str):
        snap = self.snapshot
        if snap is not None:
            df = snap["hist"].get((ticker, start_date_str))
            if df is not None:
                return df.copy()   # comme st.cache_data : chaque appelant reçoit sa propre copie
        return None

    def begin_refresh(self, run_fn):
        """Passe en mode « instantané » et lance run_fn() (qui renvoie les résultats à enregistrer)
        dans un thread, une seule fois même si plusieurs reruns arrivent pendant ce temps."""
        with self.lock:
            self.serve_stale = True
            if self.refreshing:
                return
            self.refreshing = True
        def _worker():
            results = None
            try:
                results = run_fn()
            except Exception as exc:
                self.last_error = repr(exc)
            self._finish(results)
        try:
            self._threading.Thread(target=_worker, daemon=True, name="market-refresh").start()
        except Exception:
            with self.lock:
                self.serve_stale = False
                self.refreshing = False
            raise

    def _finish(self, results):
        # on bascule d'abord (la page peut se relancer tout de suite), on enregistre ensuite
        with self.lock:
            self.serve_stale = False
            self.refreshing = False
            self.last_fresh_ts = time_module.time()
            self.epoch += 1
        if results:
            self._save_snapshot(results)

    def mark_fresh(self, results=None):
        """Appelé après une actualisation complète faite en mode classique (bloquant)."""
        with self.lock:
            self.last_fresh_ts = time_module.time()
            self.force_blocking = False
            self.serve_stale = False
        if results:
            try:
                self._threading.Thread(target=self._save_snapshot, args=(results,), daemon=True, name="market-snapshot").start()
            except Exception:
                pass

    def invalidate(self, background=False):
        """Bouton « Rafraîchir » : les caches viennent d'être vidés. background=False -> la page
        attend les cours frais ; background=True -> elle continue d'afficher l'instantané (les
        derniers cours connus, ceux qu'on vient de voir à l'écran) pendant qu'un thread récupère
        les cours frais, comme à l'ouverture. Sans instantané, on attend dans les deux cas."""
        with self.lock:
            self.last_fresh_ts = 0.0
            self.force_blocking = not background
            self.serve_stale = False

    def _save_snapshot(self, results):
        import pickle
        try:
            live = dict(results.get("live", {}))
            hist = {k: v for k, v in results.get("hist", {}).items() if v is not None and hasattr(v, "empty")}
            n_live_ok = sum(1 for v in live.values() if v is not None)
            n_hist_ok = sum(1 for v in hist.values() if not v.empty)
            # Réseau coupé / Yahoo qui bride : on ne remplace JAMAIS un bon instantané par un mauvais
            if not live or n_live_ok < 0.5 * len(live) or not hist or n_hist_ok < 0.5 * len(hist):
                return
            snap = {"ts": time_module.time(), "live": live, "hist": hist}
            tmp_path = self.path + ".tmp"
            with open(tmp_path, "wb") as f:
                pickle.dump(snap, f, protocol=pickle.HIGHEST_PROTOCOL)
            os.replace(tmp_path, self.path)
            self.snapshot = snap
        except Exception as exc:
            self.last_error = repr(exc)

@st.cache_resource(show_spinner=False)
def _swr_state():
    return _MarketSWR(_MARKET_SNAPSHOT_FILE)

def get_live_price(ticker):
    if _SWR_ENABLED:
        _s = _swr_state()
        if _s.serve_stale:
            _found, _val = _s.snapshot_live(ticker)
            if _found:
                return _val
    return _get_live_price_real(ticker)

def get_ticker_history(ticker, start_date_str):
    """Historique complet des clôtures d'un ticker depuis start_date_str (voir
    _get_ticker_history_real) ; pendant l'affichage immédiat, renvoie celui de l'instantané."""
    if _SWR_ENABLED:
        _s = _swr_state()
        if _s.serve_stale:
            _df = _s.snapshot_hist(ticker, start_date_str)
            if _df is not None:
                return _df
    return _get_ticker_history_real(ticker, start_date_str)

@st.cache_data(ttl=300, show_spinner=False)
def get_watchlist_variations(ticker):
    """Variation du prix (delta en €, % ) sur plusieurs horizons — jour, 7 jours, 30 jours,
    6 mois, 12 mois — pour un ticker de la watchlist, à partir de son historique de clôtures
    (get_ticker_history, déjà mis en cache séparément). Renvoie un dict {"jour": (delta, pct),
    "semaine": (delta, pct), "30j": (delta, pct), "6m": (delta, pct), "12m": (delta, pct)},
    chaque tuple valant (None, None) quand l'historique disponible ne remonte pas assez loin
    pour cet horizon (ex. valeur récemment introduite en bourse)."""
    result = {"jour": (None, None), "semaine": (None, None), "30j": (None, None), "6m": (None, None), "12m": (None, None)}
    if not ticker:
        return result
    # 400 jours calendaires en arrière : large marge au-delà des 365 jours nécessaires pour
    # l'horizon "12 mois", pour être sûr d'avoir au moins une clôture disponible à/avant cette
    # date même en tenant compte des jours sans cotation (week-ends, jours fériés).
    start_str = (_now_paris() - pd.Timedelta(days=400)).strftime("%Y-%m-%d")
    hist_df = get_ticker_history(ticker, start_str)
    if hist_df is None or hist_df.empty or "Close" not in hist_df.columns:
        return result
    closes = hist_df["Close"].dropna()
    if closes.empty:
        return result
    if hasattr(closes.index, "tz_localize") and closes.index.tz is not None:
        closes.index = closes.index.tz_localize(None)
    closes.index = closes.index.normalize()

    today_norm = _today_paris()
    prix_actuel = get_live_price(ticker)

    # Variation du jour : prix actuel (quasi temps réel) contre la dernière clôture disponible
    # STRICTEMENT AVANT aujourd'hui (et non la clôture du jour même, qui pourrait déjà refléter
    # le prix actuel et donner artificiellement 0 %).
    closes_avant_jour = closes[closes.index < today_norm]
    dernier_close = closes_avant_jour.iloc[-1] if not closes_avant_jour.empty else closes.iloc[-1]
    if prix_actuel is not None and dernier_close:
        result["jour"] = (prix_actuel - dernier_close, (prix_actuel - dernier_close) / dernier_close * 100)

    # Pour les horizons plus longs, on part du prix actuel s'il est disponible (sinon de la
    # dernière clôture connue), comparé à la dernière clôture disponible à ou avant la date
    # cible (aujourd'hui - N jours) — le jour exact N n'étant pas forcément un jour coté.
    ref_prix = prix_actuel if prix_actuel is not None else closes.iloc[-1]
    horizons = {"semaine": 7, "30j": 30, "6m": 182, "12m": 365}
    for cle, jours in horizons.items():
        cible = today_norm - pd.Timedelta(days=jours)
        closes_avant_cible = closes[closes.index <= cible]
        if closes_avant_cible.empty or ref_prix is None:
            continue
        prix_ref_h = closes_avant_cible.iloc[-1]
        if prix_ref_h:
            result[cle] = (ref_prix - prix_ref_h, (ref_prix - prix_ref_h) / prix_ref_h * 100)

    return result

@st.cache_data(ttl=3600, show_spinner=False)
def get_benchmark_history(ticker, start_str, end_str):
    """Historique de clôture d'un indice/benchmark, mis en cache 1h. Utilisé à la fois par le
    graphique de performance comparée et le tableau comparatif : sans ce cache, chaque
    rerun Streamlit (changement de sélection, clic sur un toggle, etc.) relançait un appel
    réseau à Yahoo Finance pour CHAQUE indice sélectionné, à CHAQUE fois — c'était la
    principale cause de lenteur du dashboard une fois plusieurs indices affichés."""
    try:
        hist = yf.Ticker(ticker).history(start=start_str, end=end_str, auto_adjust=True)["Close"]
        if hasattr(hist.index, "tz_localize") and hist.index.tz is not None:
            hist.index = hist.index.tz_localize(None)
        return hist
    except Exception:
        return pd.Series(dtype=float)

@st.cache_data(ttl=None, show_spinner=False)
def load_data():
    # Le cache est explicitement vidé (load_data.clear()) juste après chaque sauvegarde
    # réussie plus bas dans le fichier : inutile donc de passer une "signature" en argument
    # comme avec l'ancien fichier CSV (mtime) — Supabase ne fournit pas d'équivalent simple,
    # et ce n'est de toute façon plus nécessaire.
    records = _supabase_get_value("transactions", [])
    if records:
        df = pd.DataFrame(records)
        df["Date_Heure"] = pd.to_datetime(df["Date_Heure"])
        if "Rompu" not in df.columns:
            df["Rompu"] = 0.0
        if "Retenue_Source_Etrangere" not in df.columns:
            df["Retenue_Source_Etrangere"] = 0.0
        if "Remboursement_Capital" not in df.columns:
            df["Remboursement_Capital"] = 0.0
        if "Arrondi_Courtier" not in df.columns:
            # Colonne ajoutée après-coup : sert à corriger les écarts d'arrondi du courtier sur
            # les dividendes (voir k_div_arrondi plus bas). Absente des anciens enregistrements, donc 0.0
            # par défaut pour tout l'historique déjà enregistré (comportement inchangé).
            df["Arrondi_Courtier"] = 0.0
        if "Date_Rompus" not in df.columns:
            # Colonne ajoutée après-coup : pour tout l'historique déjà enregistré, on ne connaît
            # qu'une seule date par ligne SPLIT (celle du split), donc on l'utilise aussi comme
            # date de versement des rompus par défaut — comportement strictement identique à
            # avant pour ces lignes-là. Seules les NOUVELLES lignes SPLIT pourront préciser une
            # date de versement des rompus différente de la date du split.
            df["Date_Rompus"] = pd.NaT
        else:
            df["Date_Rompus"] = pd.to_datetime(df["Date_Rompus"], errors="coerce")
        df["Date_Rompus"] = df["Date_Rompus"].fillna(df["Date_Heure"])
        return df
    else:
        return pd.DataFrame(
            columns=[
                "Date_Heure", "Type", "Nom", "Ticker",
                "Quantité", "Prix Unitaire (€)", "Commission (€)",
                "TTF (€)", "Frais Totaux (€)", "Rompu", "Retenue_Source_Etrangere",
                "Remboursement_Capital", "Arrondi_Courtier", "Date_Rompus"
            ]
        )

df_transactions = load_data()

# ==========================================
# PRÉCHARGEMENT PARALLÈLE DES DONNÉES DE MARCHÉ
# ==========================================
# Les fonctions get_live_price sont mises en cache par Streamlit
# (@st.cache_data), mais restent appelées ticker par ticker, en séquentiel, plus loin
# dans le script. Sur un cache "froid" (premier chargement, ou après expiration du TTL),
# cela se traduit par autant d'allers-retours réseau successifs qu'il y a de valeurs,
# ce qui explique la lenteur au démarrage. La fonction ci-dessous "chauffe" ces caches
# en parallèle (plusieurs tickers interrogés en même temps) : les valeurs calculées et
# affichées restent strictement identiques, seul le temps d'attente change.
_PREFETCH_MAX_WORKERS = 20  # requêtes Yahoo simultanées (augmenter prudemment : trop de parallélisme peut être bridé par Yahoo)

def _prefetch_market_data(tickers, start_date_str=None, extra_live_tickers=(), getters=None, timeout=None):
    """Charge en parallèle cours en direct, secteur/pays et historiques. Renvoie
    {"live": {ticker: cours}, "hist": {(ticker, début): DataFrame}} pour ce qui a abouti (sert à
    enregistrer l'instantané). `getters` = (live, info, hist) permet d'appeler directement les
    versions réelles pendant l'actualisation en arrière-plan ; `timeout` (secondes) n'est utilisé
    que dans ce cas, pour ne jamais rester bloqué si le réseau ne répond plus."""
    tickers = sorted({t for t in tickers if t and t not in _FAILED_TICKERS})
    # Valeurs de la watchlist dont l'alerte « zone d'achat » demande le cours en direct : elles
    # étaient interrogées une par une, en séquence, plus loin dans le script (barre d'alertes) ;
    # on les charge maintenant en parallèle avec le reste. Seul le cours en direct est demandé.
    extra_live = sorted({t for t in extra_live_tickers if t and t not in _FAILED_TICKERS and t not in tickers})
    results = {"live": {}, "hist": {}}
    if not tickers and not extra_live:
        return results
    _g_live, _g_info, _g_hist = getters if getters else (get_live_price, None, get_ticker_history)
    # Les 3 types d'appels (prix live, infos secteur/pays, historique complet) sont soumis
    # d'un coup au même pool de threads via submit(), au lieu d'un executor.map() par type
    # exécuté l'un après l'autre : map() attend la fin de tous les tickers avant de rendre la
    # main, donc 3 map() successifs = 3 vagues séquentielles. Avec submit(), les ~3x plus
    # d'appels partent tous en même temps et se recouvrent, ce qui réduit le temps d'attente
    # total au démarrage à froid (cache expiré) au lieu de l'additionner.
    n_calls = (len(tickers) * (2 if start_date_str else 1) + len(extra_live)) or 1
    _n_workers = min(_PREFETCH_MAX_WORKERS, n_calls)
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=_n_workers)
    _jobs = []   # (catégorie, clé, future)
    try:
        for t in tickers:
            _jobs.append(("live", t, executor.submit(_g_live, t)))
        for t in extra_live:
            _jobs.append(("live", t, executor.submit(_g_live, t)))
        if start_date_str:
            for t in tickers:
                _jobs.append(("hist", (t, start_date_str), executor.submit(_g_hist, t, start_date_str)))
        concurrent.futures.wait([j[2] for j in _jobs], timeout=timeout)
    finally:
        # sans délai maximal : on attend la fin de tous les appels, comme avant (with executor:)
        executor.shutdown(wait=(timeout is None), cancel_futures=True)
    for kind, key, fut in _jobs:
        if kind in ("live", "hist") and fut.done() and not fut.cancelled() and fut.exception() is None:
            results[kind][key] = fut.result()
    return results

_tickers_a_precharger = (
    df_transactions[~df_transactions["Type"].isin(["APPORT", "RETRAIT"])]["Ticker"]
    .dropna().unique().tolist()
    if not df_transactions.empty else []
)
_start_date_str_precharge = (
    df_transactions["Date_Heure"].min().normalize().strftime("%Y-%m-%d")
    if not df_transactions.empty else None
)
# get_live_price / get_ticker_history sont déjà mis en cache par Streamlit
# (10 min / 24 h / 5 min de TTL) : une fois le cache chaud, les relire ne coûte quasiment rien.
# Mais Streamlit relance TOUT le script à chaque interaction (y compris chaque frappe dans le
# formulaire "Nouvelle opération", qui est une simple fenêtre @st.dialog et pas un st.form) : sans
# ce garde-fou, ce bloc rappelait quand même _prefetch_market_data (création d'un pool de
# threads + un aller-retour au cache par ticker par type de donnée) et ré-affichait le spinner
# "Récupération des cours..." à CHAQUE frappe, donnant l'impression d'un rechargement réseau
# alors qu'il n'y en a pas besoin. On ne relance ce préchargement qu'une fois toutes les
# _MARKET_PREFETCH_MIN_INTERVAL secondes maximum (en-deçà du plus petit TTL ci-dessus), ce qui
# supprime cette latence perçue sur toutes les interactions du formulaire sans jamais servir de
# données plus vieilles que ce que les caches auraient de toute façon renvoyé.
_MARKET_PREFETCH_MIN_INTERVAL = 540  # secondes (juste sous le TTL de 600 s des cours en direct)
_now_ts = time_module.time()
_last_prefetch_ts = st.session_state.get("_last_market_prefetch_ts", 0.0)
_wl_tickers_alertes = [
    _it.get("ticker") for _it in app_config.get("watchlist", [])
    if _it.get("ticker") and _it.get("zone_achat")
]
_swr = _swr_state() if _SWR_ENABLED else None
if (_tickers_a_precharger or _wl_tickers_alertes) and (_now_ts - _last_prefetch_ts > _MARKET_PREFETCH_MIN_INTERVAL):
    if _swr is not None and _swr.can_serve_stale():
        # Caches de cours froids ET un instantané existe : on affiche tout de suite à partir de
        # l'instantané et on actualise en arrière-plan (les getters réels remplissent les caches).
        try:
            _bg_tickers, _bg_start, _bg_wl = list(_tickers_a_precharger), _start_date_str_precharge, list(_wl_tickers_alertes)
            _swr.begin_refresh(lambda: _prefetch_market_data(
                _bg_tickers, _bg_start, _bg_wl,
                getters=(_get_live_price_real, None, _get_ticker_history_real),
                timeout=_SWR_REFRESH_TIMEOUT))
            st.session_state["_last_market_prefetch_ts"] = _now_ts
        except Exception:
            pass   # impossible de démarrer un thread : on retombe sur l'attente classique ci-dessous
    if _swr is None or not _swr.serve_stale:
        # Caches encore chauds (dernière actualisation complète < _MARKET_FRESH_WINDOW) : relecture quasi instantanée,
        # donc sans barre de chargement (elle apparaissait à chaque changement d'onglet après quelques minutes).
        _caches_chauds = _swr is not None and (time_module.time() - _swr.last_fresh_ts) <= _MARKET_FRESH_WINDOW
        _spin_ctx = contextlib.nullcontext()   # pas de barre dans la page : seul le « Running… » natif de Streamlit s'affiche
        with _spin_ctx:
            _prefetch_results = _prefetch_market_data(_tickers_a_precharger, _start_date_str_precharge, _wl_tickers_alertes)
        st.session_state["_last_market_prefetch_ts"] = _now_ts
        if _swr is not None:
            _swr.mark_fresh(_prefetch_results)

_swr_epoch_at_start = _swr.epoch if _swr is not None else 0
if _swr is not None and _swr.serve_stale:
    @st.fragment(run_every=2)
    def _swr_banner():
        _s = _swr_state()
        if _s.epoch == _swr_epoch_at_start:
            _snap = _s.snapshot
            _quand = datetime.fromtimestamp(_snap["ts"]).strftime("%d/%m à %H:%M") if _snap else "?"
            st.info(f"🔄 Actualisation des cours en cours… Les chiffres affichés reposent pour l'instant sur les derniers cours connus ({_quand}) ; la page se mettra à jour toute seule dans quelques secondes.")
        else:
            st.rerun()   # actualisation terminée : relance toute l'application avec les cours frais
    _swr_banner()

# ==========================================
# 2. MOTEUR DE CALCUL DES POSITIONS & PERF
# ==========================================
@st.cache_data(ttl=300, show_spinner=False)
def compute_portfolio_metrics_cached(df_in, target_datetime=None):
    df = df_in.copy()
    if df.empty:
        return pd.DataFrame(), 0, 0, 0, 0, 0, 0

    if target_datetime is not None:
        df = df[df["Date_Heure"] <= target_datetime]

    if df.empty:
        return pd.DataFrame(), 0, 0, 0, 0, 0, 0

    portfolio_summary = []
    total_invested_global = 0
    total_current_value_global = 0
    # On ne compte que les frais des ACHATs/VENTEs (vrais frais de courtage/TTF). Sur les lignes
    # DIVIDENDE, la colonne "Frais Totaux (€)" contient en réalité la retenue à la source
    # étrangère (déjà déduite séparément dans le calcul du dividende net ci-dessous via
    # "Retenue_Source_Etrangere") : ce n'est pas un frais de courtage, et la sommer ici en plus
    # gonflait artificiellement le total "Frais Totaux" affiché sur le tableau de bord.
    total_fees_global = df[df["Type"].isin(["ACHAT", "VENTE"])]["Frais Totaux (€)"].sum()
    total_dividends_global = 0
    total_realized_pnl = 0
    total_cost_basis_global = 0  # Capital total réellement engagé sur toute la durée de vie du
    # portefeuille (achats cumulés, y compris sur des positions aujourd'hui totalement soldées),
    # à ne pas confondre avec total_invested_global qui ne compte que le capital ENCORE investi
    # aujourd'hui. C'est ce total "lifetime" qu'il faut utiliser comme dénominateur de la
    # performance globale, sinon une position soldée avec plus-value gonfle artificiellement le %.

    name_map = df[~df["Type"].isin(["APPORT", "RETRAIT"])].groupby('Ticker')['Nom'].last().to_dict()
    df_actions = df[~df["Type"].isin(["APPORT", "RETRAIT"])].copy()
    is_historical_check = (target_datetime is not None)

    def custom_sort_key(row):
        t = row["Type"]
        if t == "SPLIT":
            h = time(0, 0, 0)
        else:
            h = row["Date_Heure"].time()
        return (row["Date_Heure"].date(), h)

    for ticker, group in df_actions.groupby("Ticker"):
        group_sorted = sorted(group.to_dict('records'), key=custom_sort_key)
        
        total_shares = 0
        total_invested = 0
        total_achats_historiques = 0 
        total_vendu_action = 0
        dividends = 0
        realized_pnl = 0
        pnl_round_trips = []
        first_buy_date = None
        sold_out_date = None
        cycle_start = None          # début du cycle de détention en cours (achat sur ligne à 0 titre)
        secondes_detention = 0.0     # temps de détention exact cumulé (en secondes)
        jours_detenus = set()        # jours calendaires où au moins un titre était détenu (comptés une seule fois)
        total_commissions_ticker = 0
        total_ttf_ticker = 0
        nb_mouvements_ticker = 0

        for row in group_sorted:
            t = row["Type"]
            qty = row["Quantité"]
            p = row["Prix Unitaire (€)"]
            f = row["Frais Totaux (€)"]
            comm = row.get("Commission (€)", 0.0)
            ttf_val = row.get("TTF (€)", 0.0)
            rompu = row.get("Rompu", 0.0)
            ret_etr = row.get("Retenue_Source_Etrangere", 0.0)
            if t in ("ACHAT", "VENTE"):
                nb_mouvements_ticker += 1

            if t == "ACHAT":
                if first_buy_date is None:
                    first_buy_date = row["Date_Heure"]
                if cycle_start is None:
                    cycle_start = row["Date_Heure"]
                sold_out_date = None
                total_shares += qty
                total_invested += (qty * p) + f
                total_achats_historiques += (qty * p) + f
                total_commissions_ticker += comm
                total_ttf_ticker += ttf_val
            elif t == "VENTE":
                sale_revenue = (qty * p) - f  
                total_vendu_action += sale_revenue
                total_commissions_ticker += comm
                total_ttf_ticker += ttf_val
                if total_shares > 0:
                    current_pru = total_invested / total_shares if total_shares > 0 else 0
                    cost_basis_sold = qty * current_pru
                    rt_pnl = sale_revenue - cost_basis_sold
                    realized_pnl += rt_pnl
                    pnl_round_trips.append(rt_pnl)

                    total_shares -= qty
                    total_invested = total_shares * current_pru
                    if total_shares <= 0.0001:
                        sold_out_date = row["Date_Heure"]
                        if cycle_start is not None:
                            # Cycle terminé : tous ses jours (début et fin inclus) sont détenus. Un aller-retour
                            # dans la même journée = 1 jour ; un second aller-retour un autre jour = 2 au total.
                            jours_detenus.update(pd.date_range(pd.Timestamp(cycle_start).normalize(), pd.Timestamp(row["Date_Heure"]).normalize()))
                            secondes_detention += max((pd.Timestamp(row["Date_Heure"]) - pd.Timestamp(cycle_start)).total_seconds(), 0.0)
                            cycle_start = None
            elif t == "SPLIT":
                _rompu_deja_compte = False
                # Un rompu dont la date de versement (Date_Rompus) est encore dans le futur n'a
                # pas encore été crédité par le courtier : on ne le compte donc pas encore dans
                # les dividendes reçus, sous peine de gonfler ce total (et la performance qui en
                # découle) avant que l'argent ne soit réellement arrivé.
                _date_rompu_row = row.get("Date_Rompus")
                if pd.isnull(_date_rompu_row):
                    _date_rompu_row = row["Date_Heure"]
                _rompu_deja_verse = _date_rompu_row <= _now_paris()
                if total_shares > 0:
                    brute_shares = total_shares * qty
                    integer_shares = int(brute_shares)
                    fractional_shares = brute_shares - integer_shares
                    
                    # _rompu_deja_compte évite de compter deux fois le même rompu : une fois
                    # ci-dessous (part fractionnaire calculée à partir des actions détenues) et
                    # une seconde fois via la colonne "Rompu" de la ligne SPLIT elle-même.
                    if fractional_shares > 1e-6:
                        _rompu_deja_compte = True
                        total_shares = integer_shares
                        if pd.notnull(rompu) and rompu > 0:
                            rompu_val_cash = rompu
                        else:
                            current_p_temp = get_live_price(ticker) or 0
                            rompu_val_cash = fractional_shares * current_p_temp
                        if _rompu_deja_verse:
                            dividends += rompu_val_cash
                            total_dividends_global += rompu_val_cash
                    else:
                        total_shares = integer_shares
                        
                if pd.notnull(rompu) and rompu > 0 and not _rompu_deja_compte and _rompu_deja_verse:
                    dividends += rompu
                    total_dividends_global += rompu
            elif t == "DIVIDENDE":
                arrondi_courtier_div = row.get("Arrondi_Courtier", 0.0)
                arrondi_courtier_div = arrondi_courtier_div if pd.notnull(arrondi_courtier_div) else 0.0
                net_div = p - ret_etr - comm + arrondi_courtier_div
                dividends += net_div
                total_dividends_global += net_div
                remb_capital = row.get("Remboursement_Capital", 0.0)
                if pd.notnull(remb_capital) and remb_capital > 0:
                    # Remboursement de capital versé en même temps qu'un dividende (ex. Schneider
                    # Electric) : il ne s'agit pas d'un gain mais d'une restitution partielle du
                    # capital investi, donc cela fait mécaniquement baisser le PRU, comme un
                    # remboursement de prime le ferait sur un contrat.
                    total_invested = max(0.0, total_invested - remb_capital)
                    total_achats_historiques = max(0.0, total_achats_historiques - remb_capital)

        total_realized_pnl += realized_pnl

        if total_shares > 0.0001 or abs(realized_pnl) > 0.001 or dividends > 0.001 or total_achats_historiques > 0:
            net_pru = total_invested / total_shares if total_shares > 0.0001 else 0
            
            if is_historical_check:
                current_price = get_historical_price_at(ticker, target_datetime) or net_pru
            else:
                current_price = get_live_price(ticker) or net_pru
            
            if current_price is None or np.isnan(current_price):
                current_price = net_pru

            current_value = total_shares * current_price
            hidden_pnl = current_value - total_invested if total_shares > 0.0001 else 0
            total_gain_with_div = hidden_pnl + dividends + realized_pnl
            
            if total_shares <= 0.0001:
                base_perf = total_achats_historiques if total_achats_historiques > 0 else 1.0
            else:
                base_perf = total_invested if total_invested > 0 else 1.0

            perf_pct = (total_gain_with_div / base_perf) * 100 if base_perf > 0 else 0.0
            active_perf_pct = (hidden_pnl / total_invested) * 100 if total_invested > 0 else 0.0

            yoc = (dividends / total_invested) * 100 if total_invested > 0 else 0
            avg_rt_pnl = np.mean(pnl_round_trips) if pnl_round_trips else 0

            total_invested_global += total_invested
            total_current_value_global += current_value
            total_cost_basis_global += total_achats_historiques

            comm_pct_val = (total_commissions_ticker / total_invested * 100) if total_invested > 0 else 0.0

            portfolio_summary.append({
                "Nom": name_map.get(ticker, ticker),
                "Ticker": ticker,
                "Quantité": round(total_shares, 4),
                "PRU Net (€)": net_pru,
                "Prix Actuel (€)": current_price,
                "Valeur Actuelle (€)": current_value,
                "Capital Investi (€)": total_invested,
                "YoC (%) **": round(yoc, 2),
                "Nb Mouvements": nb_mouvements_ticker,
                "Nb Allers-Retours": len(pnl_round_trips),
                "Gain Moyen AR (€)": avg_rt_pnl,
                "Gain Réalisé (€)": realized_pnl,
                "Gain Latent (€)": hidden_pnl,
                "Dividendes Reçus (€)": dividends,
                "Gain Total Global (€)": total_gain_with_div,
                "Performance (%)": perf_pct,
                "Performance Active (%)": active_perf_pct,
                "Jours Détention": len(
                    jours_detenus.union(
                        pd.date_range(pd.Timestamp(cycle_start).normalize(),
                                      max(pd.Timestamp(target_datetime if is_historical_check else _now_paris()).normalize(),
                                          pd.Timestamp(cycle_start).normalize()))
                        if (cycle_start is not None and total_shares > 0.0001) else []
                    )
                ),
                "Secondes Détention": secondes_detention + (
                    max((pd.Timestamp(target_datetime if is_historical_check else _now_paris()) - pd.Timestamp(cycle_start)).total_seconds(), 0.0)
                    if (cycle_start is not None and total_shares > 0.0001) else 0.0
                ),
                "Commission Pct": comm_pct_val,
                "TTF Pct": total_ttf_ticker,
            })

    df_res = pd.DataFrame(portfolio_summary)
    if not df_res.empty and "Gain Total Global (€)" in df_res.columns:
        df_res = df_res.sort_values(by="Gain Total Global (€)", ascending=False)

    return df_res, total_invested_global, total_current_value_global, total_fees_global, total_dividends_global, total_realized_pnl, total_cost_basis_global

def compute_portfolio_metrics(df, target_datetime=None):
    return compute_portfolio_metrics_cached(df, target_datetime)

@st.cache_data(ttl=300, show_spinner=False)
def compute_cash_actuel_cached(df_in):
    """Calcule uniquement le solde ACTUEL de la poche espèces du PEA, en rejouant l'impact de
    chaque transaction sur le cash (même logique que get_portfolio_history_cached), mais SANS
    reconstruire de série quotidienne ni interroger l'historique de cours (yfinance) sur toute
    la période. Beaucoup plus rapide que get_portfolio_history_cached quand on n'a besoin que
    du solde final (ex. pour les exports), pas de son évolution jour par jour."""
    if df_in is None or df_in.empty:
        return 0.0

    df_mouv = df_in.copy()
    mask_split = df_mouv["Type"] == "SPLIT"
    if "Date_Rompus" in df_mouv.columns:
        df_mouv.loc[mask_split, "Date_Heure"] = df_mouv.loc[mask_split, "Date_Rompus"].fillna(df_mouv.loc[mask_split, "Date_Heure"])
    df_mouv = df_mouv.sort_values("Date_Heure")

    cash = 0.0
    # to_dict("records") plutôt que .iterrows() : mêmes valeurs, sans reconstruire une Series
    # pandas à chaque ligne.
    for row in df_mouv.to_dict("records"):
        t = row["Type"]
        qty = row["Quantité"]
        p = row["Prix Unitaire (€)"]
        f = row["Frais Totaux (€)"]
        comm = row.get("Commission (€)", 0.0)
        ret_etr = row.get("Retenue_Source_Etrangere", 0.0)
        rompu = row.get("Rompu", 0.0)

        if t == "APPORT":
            cash = _round_cash(cash, qty)
        elif t == "RETRAIT":
            cash = _round_cash(cash, -qty)
        elif t == "ACHAT":
            # Montant débité arrondi au centime, exactement comme le fait le courtier sur
            # l'avis d'opéré, AVANT d'être retranché du cash cumulé (voir _montant_ordre et
            # _round_cash) : sans cela, les résidus de sous-centime (prix unitaire à 3-4
            # décimales × quantité tombant entre deux centimes, ex. 106,225 €) s'accumulent au
            # fil des transactions et finissent par créer un écart de quelques centimes avec le
            # solde réel du courtier.
            cash = _round_cash(cash, -_montant_ordre(qty, p, f))
        elif t == "VENTE":
            cash = _round_cash(cash, _montant_ordre(qty, p, -f))
        elif t == "DIVIDENDE":
            remb = row.get("Remboursement_Capital", 0.0)
            remb = remb if pd.notnull(remb) else 0.0
            arrondi_courtier = row.get("Arrondi_Courtier", 0.0)
            arrondi_courtier = arrondi_courtier if pd.notnull(arrondi_courtier) else 0.0
            cash = _round_cash(cash, p, -ret_etr, -comm, remb, arrondi_courtier)
        elif t == "SPLIT":
            if pd.notnull(rompu) and rompu > 0:
                cash = _round_cash(cash, rompu)

    return cash

def compute_cash_actuel(df):
    return compute_cash_actuel_cached(df)

@st.cache_data(ttl=300, show_spinner=False)
def compute_realized_pnl_par_vente_cached(df_in):
    """Rejoue exactement le même calcul de plus-value réalisée (coût moyen pondéré, PRU
    recalculé à chaque ACHAT/VENTE/SPLIT) que compute_portfolio_metrics_cached, mais renvoie
    une ligne par VENTE avec sa date/heure précise et le gain réalisé associé à CETTE vente
    (au lieu du seul total cumulé par action). Sert à répartir les plus-values actées par
    tranche horaire de séance (bâtons "Plus-Values Actées par Tranche Horaire")."""
    df = df_in.copy()
    if df.empty:
        return pd.DataFrame(columns=["Date_Heure", "Ticker", "Gain Réalisé (€)", "Gain Réalisé (%)"])

    df_actions = df[~df["Type"].isin(["APPORT", "RETRAIT"])].copy()

    def custom_sort_key(row):
        h = time(0, 0, 0) if row["Type"] == "SPLIT" else row["Date_Heure"].time()
        return (row["Date_Heure"].date(), h)

    records = []
    for ticker, group in df_actions.groupby("Ticker"):
        group_sorted = sorted(group.to_dict('records'), key=custom_sort_key)
        total_shares = 0.0
        total_invested = 0.0

        for row in group_sorted:
            t = row["Type"]
            qty = row["Quantité"]
            p = row["Prix Unitaire (€)"]
            f = row["Frais Totaux (€)"]

            if t == "ACHAT":
                total_shares += qty
                total_invested += (qty * p) + f
            elif t == "VENTE":
                sale_revenue = (qty * p) - f
                if total_shares > 0:
                    current_pru = total_invested / total_shares if total_shares > 0 else 0
                    cost_basis_sold = qty * current_pru
                    rt_pnl = sale_revenue - cost_basis_sold
                    rt_pnl_pct = (rt_pnl / cost_basis_sold * 100) if cost_basis_sold > 0 else 0.0
                    records.append({
                        "Date_Heure": row["Date_Heure"],
                        "Ticker": ticker,
                        "Gain Réalisé (€)": rt_pnl,
                        "Gain Réalisé (%)": rt_pnl_pct,
                    })
                    total_shares -= qty
                    total_invested = total_shares * current_pru
            elif t == "SPLIT":
                if total_shares > 0:
                    brute_shares = total_shares * qty
                    integer_shares = int(brute_shares)
                    total_shares = integer_shares
                    # total_invested n'est volontairement pas modifié ici : c'est bien ce qui
                    # fait mécaniquement baisser le PRU après un split, exactement comme dans
                    # compute_portfolio_metrics_cached.

    return pd.DataFrame(records)

def compute_realized_pnl_par_vente(df):
    return compute_realized_pnl_par_vente_cached(df)

@st.cache_data(ttl=300, show_spinner=False)
def detect_ttf_anomalies_cached(df_in):
    """Détecte automatiquement, sur TOUT l'historique des transactions, les journées où de la
    TTF a été réglée à l'achat sur des titres finalement revendus le même jour. La TTF française
    n'est en réalité prélevée qu'une fois par jour, uniquement sur les titres éligibles encore
    détenus EN FIN DE JOURNÉE : si 3 titres sont achetés puis 1 revendu le même jour, la TTF
    n'est due que sur les 2 titres restants, pas sur 0 ni sur les 3 initialement achetés.
    Renvoie une liste d'anomalies (une par ticker/jour concerné), avec le montant de TTF
    actuellement enregistré et celui réellement dû."""
    anomalies = []
    if df_in is None or df_in.empty:
        return anomalies

    df_ops = df_in[df_in["Type"].isin(["ACHAT", "VENTE"])].copy()
    if df_ops.empty:
        return anomalies
    df_ops["_date"] = df_ops["Date_Heure"].dt.date

    name_map = df_in[~df_in["Type"].isin(["APPORT", "RETRAIT"])].groupby("Ticker")["Nom"].last().to_dict()

    # Les agrégats (quantités achetées avec TTF, TTF enregistrée, quantités vendues) sont calculés
    # sur des tableaux numpy, groupe par groupe, au lieu de fabriquer un sous-DataFrame puis
    # filtrer 3 fois dedans pour CHAQUE couple (ticker, jour) — c'était le principal coût de ce
    # contrôle (il tourne à chaque modification des transactions). Les sous-DataFrames ne sont
    # plus construits que pour les rares groupes réellement en anomalie, où le détail
    # ligne par ligne est calculé exactement comme avant. ngroup() numérote les groupes dans
    # l'ordre exact où groupby() les itère : la liste d'anomalies garde donc le même ordre.
    _types_ttf = df_ops["Type"].to_numpy()
    _qte_ttf = df_ops["Quantité"].to_numpy(dtype=float)
    _ttf_ttf = df_ops["TTF (€)"].fillna(0).to_numpy(dtype=float)
    _ticker_ttf = df_ops["Ticker"].to_numpy()
    _date_ttf = df_ops["_date"].to_numpy()
    _gid_ttf = df_ops.groupby(["Ticker", "_date"]).ngroup().to_numpy()
    _rows_par_groupe = {}
    for _pos_ttf, _g_ttf in enumerate(_gid_ttf):
        if _g_ttf >= 0:
            _rows_par_groupe.setdefault(_g_ttf, []).append(_pos_ttf)

    for _g_ttf in sorted(_rows_par_groupe):
        _ix_ttf = np.asarray(_rows_par_groupe[_g_ttf])
        _t_g = _types_ttf[_ix_ttf]
        _mask_achat_ttf = (_t_g == "ACHAT") & (_ttf_ttf[_ix_ttf] > 0)
        if not _mask_achat_ttf.any():
            continue
        _q_g = _qte_ttf[_ix_ttf]
        qte_achat_ttf = float(np.nansum(_q_g[_mask_achat_ttf]))
        ttf_enregistre = float(np.nansum(_ttf_ttf[_ix_ttf][_mask_achat_ttf]))
        if qte_achat_ttf <= 0.0001:
            continue

        qte_vendue_jour = float(np.nansum(_q_g[_t_g == "VENTE"]))
        qte_restante_ttf = max(0.0, qte_achat_ttf - qte_vendue_jour)
        ratio_ttf = qte_restante_ttf / qte_achat_ttf
        ttf_du = round(ttf_enregistre * ratio_ttf, 2)

        if abs(ttf_du - round(ttf_enregistre, 2)) > 0.005:
            ticker = _ticker_ttf[_ix_ttf[0]]
            jour = _date_ttf[_ix_ttf[0]]
            groupe = df_ops.iloc[_ix_ttf]
            achats_ttf = groupe[(groupe["Type"] == "ACHAT") & (groupe["TTF (€)"].fillna(0) > 0)]
            # Détail ligne par ligne (une ligne d'achat = une heure) : le même ratio de
            # correction s'applique à chaque achat individuel du jour, pour pouvoir indiquer à
            # l'utilisateur, achat par achat, l'ancien et le nouveau montant de TTF à saisir.
            achats_ttf_sorted = achats_ttf.sort_values("Date_Heure")
            lignes_ttf = [
                {
                    "heure_str": r["Date_Heure"].strftime("%H:%M:%S"),
                    "ttf_avant_ligne": round(float(r["TTF (€)"]), 2),
                    "ttf_apres_ligne": round(float(r["TTF (€)"]) * ratio_ttf, 2),
                }
                for _, r in achats_ttf_sorted.iterrows()
            ]
            heures_list = [l["heure_str"] for l in lignes_ttf]
            if len(heures_list) == 1:
                heures_str = heures_list[0]
            else:
                heures_str = ", ".join(heures_list[:-1]) + " et " + heures_list[-1]

            anomalies.append({
                "cle": f"{ticker}_{jour.isoformat()}",
                "ticker": ticker,
                "nom": name_map.get(ticker, ticker),
                "date_str": jour.strftime("%d/%m/%Y"),
                "date_str_dash": jour.strftime("%d-%m-%Y"),
                "ttf_enregistre": round(ttf_enregistre, 2),
                "ttf_du": ttf_du,
                "lignes_ttf": lignes_ttf,
                "heures_str": heures_str,
            })

    return anomalies

def detect_ttf_anomalies(df):
    return detect_ttf_anomalies_cached(df)

# Quand une actualisation en arrière-plan vient de se terminer, les résultats mis en cache
# pendant l'affichage immédiat (calculés avec les anciens cours) sont invalidés ici, une seule
# fois par session ; les deux fonctions d'historique le sont un peu plus bas (elles ne sont pas
# encore définies à ce stade du script).
_epoch_now = _swr.epoch if _swr is not None else 0
if "_swr_seen_epoch_metrics" not in st.session_state:
    st.session_state["_swr_seen_epoch_metrics"] = _epoch_now
elif st.session_state["_swr_seen_epoch_metrics"] != _epoch_now:
    compute_portfolio_metrics_cached.clear()
    get_watchlist_variations.clear()
    st.session_state["_swr_seen_epoch_metrics"] = _epoch_now

with contextlib.nullcontext():
    df_port, tot_invested, tot_value_actions, tot_fees, tot_dividends, tot_realized_pnl, tot_cost_basis_global = compute_portfolio_metrics(df_transactions)

# Pré-calculs pour le formulaire "Nouvelle opération" : la liste des actions possédées/de tout
# l'historique, et les dictionnaires nom -> ticker / nom -> quantité, sont utilisés à CHAQUE
# ouverture du formulaire ET à chaque interaction avec un champ à l'intérieur (le formulaire
# tourne dans un st.fragment/st.dialog, donc chaque frappe ou sélection relance toute la
# fonction du dialogue). Les calculer ici, une seule fois par exécution complète du script
# (donc pas à chaque frappe dans le formulaire), au lieu de les refaire à chaque rerun du
# dialogue, accélère nettement son ouverture et sa saisie. La boucle .iterrows() d'origine est
# en plus remplacée par une construction vectorisée (set_index().to_dict()), bien plus rapide.
_actions_possedees_precalc = (
    sorted(df_port[df_port["Quantité"] > 0.0001]["Nom"].tolist()) if not df_port.empty else []
)
_all_actions_historique_precalc = (
    sorted(df_transactions[~df_transactions["Nom"].isin(["Compte Courant", ""])]["Nom"].dropna().unique().tolist())
    if not df_transactions.empty else []
)
if not df_port.empty:
    _ticker_by_name_precalc = df_port.set_index("Nom")["Ticker"].to_dict()
    _qty_by_name_precalc = df_port.set_index("Nom")["Quantité"].to_dict()
else:
    _ticker_by_name_precalc = {}
    _qty_by_name_precalc = {}

# ==========================================
# 1. BARRE LATÉRALE - OPÉRATIONS
# ==========================================
# Le réglage d'affichage (masquer les montants) est affiché directement
# sur le tableau de bord principal, juste sous les infos du courtier (cf. plus bas).

_OP_TYPE_LABELS = {
    "ACHAT": "🛒  Achat",
    "APPORT": "💰  Apport",
    "RETRAIT": "💸  Retrait",
    "VENTE": "📤  Vente",
    "DIVIDENDE": "💶  Dividende",
    "SPLIT": "🔀  Split/Regroupement",
}

def _req_field(border_key, widget_key, default=None, track=None):
    """Encadré rouge léger, posé uniquement autour du champ (jamais du titre), tant que
    la valeur du champ est vide. Dès qu'une valeur est saisie (ou pré-remplie via un
    paramètre value= par défaut, ex. ticker connu d'une action déjà possédée), l'encadré
    disparaît automatiquement. 'default' doit correspondre exactement à la valeur value=
    transmise au widget, pour que la toute première apparition du champ (avant que
    st.session_state ne soit initialisé) évalue le bon état. Si 'track' (une liste) est
    fourni, la clé du widget y est ajoutée : elle sert à valider, juste avant
    l'enregistrement, que tous les champs obligatoires effectivement affichés sont remplis."""
    if track is not None:
        track.append(widget_key)
    if widget_key in st.session_state:
        current = st.session_state.get(widget_key)
    else:
        current = default
    is_empty = current is None or current == ""
    if is_empty:
        return st.container(key=border_key)
    return contextlib.nullcontext()

def _field_label(text, help_text=None):
    """Affiche le titre stylé d'un champ du formulaire. Si help_text est fourni, ajoute une
    petite icône ℹ️ affichant une infobulle native du navigateur (attribut HTML title) au
    survol. Nécessaire car les widgets de ce formulaire utilisent label_visibility="collapsed"
    (pour ne pas dupliquer ce titre au-dessus du champ) : or Streamlit n'affiche l'infobulle du
    paramètre help= d'un widget QUE si son label est "visible" — avec un label "collapsed", ce
    help= est silencieusement ignoré et aucune infobulle n'apparaît. Cette icône, associée au
    titre stylé (toujours visible, lui), est donc le seul moyen de proposer une infobulle sur
    ces champs."""
    help_html = ""
    if help_text:
        help_txt_attr = help_text.replace('"', "&quot;")
        help_html = (
            f' <span title="{help_txt_attr}" style="cursor: help; font-size: 0.85em; '
            f'color: #64748b;">ℹ️</span>'
        )
    st.markdown(f'<div class="op-card-title" style="margin-top: 10px;">{text}{help_html}</div>', unsafe_allow_html=True)

# ==========================================
# IMPORT DE DOCUMENTS DU COURTIER (pré-remplissage du formulaire "Nouvelle opération")
# ==========================================
_SENTINEL_NOUVEAU = "➕ Ajouter un nouveau nom..."

# Clés des widgets du formulaire, remises à zéro avant chaque pré-remplissage pour ne pas garder
# les valeurs d'un import précédent (valeur par défaut : None, sauf champs texte : "").
_IMPORT_TEXT_KEYS = ["k_achat_nom_new", "k_achat_ticker_new", "k_vente_nom_new", "k_vente_ticker_new",
                     "k_div_nom_new", "k_div_ticker_new", "k_split_nom_new", "k_split_ticker_new"]
_IMPORT_OTHER_KEYS = ["k_achat_nom", "k_achat_qty", "k_achat_prix", "k_achat_comm", "k_achat_ttf",
                      "k_vente_nom", "k_vente_qty", "k_vente_prix", "k_vente_comm",
                      "k_apport_montant", "k_retrait_montant",
                      "k_div_nom", "k_div_qty_new", "k_div_qty_vide", "k_div_montant", "k_div_retenue",
                      "k_div_remb", "k_div_arrondi",
                      "k_split_nom", "k_split_facteur_new", "k_split_facteur_vide", "k_split_rompu",
                      "k_split_rompu_date", "k_date_simple", "k_date_full", "k_heure_full"]

def _anthropic_key():
    try:
        return st.secrets.get("ANTHROPIC_API_KEY", "")
    except Exception:
        return ""

def _import_build_updates(op, all_actions, owned):
    """Traduit une opération lue dans un document en valeurs de widgets du formulaire.
    Retourne (dict {clé_widget: valeur}, nom_connu_ou_None)."""
    u = {k: "" for k in _IMPORT_TEXT_KEYS}
    u.update({k: None for k in _IMPORT_OTHER_KEYS})
    u["k_op_type"] = op.type
    alias = ((app_config or {}).get("import_aliases") or {}).get(di._norm(op.name))
    known = {"name": None}

    def choose(options, key_sel, key_new, key_tick_new):
        pool = list(options)
        name = alias["nom"] if (alias and alias.get("nom") in pool) else di.match_name(op.name, pool)[0]
        if name:
            u[key_sel] = name
            known["name"] = name
        elif key_sel == "k_achat_nom":
            # Achat : case unique (liste + saisie libre) -> le nouveau nom est écrit directement dans la case.
            u[key_sel] = (alias or {}).get("nom") or op.name
            if alias and alias.get("ticker"):
                u[key_tick_new] = alias["ticker"]
        else:
            u[key_sel] = _SENTINEL_NOUVEAU
            u[key_new] = (alias or {}).get("nom") or op.name
            if alias and alias.get("ticker"):
                u[key_tick_new] = alias["ticker"]
        return known["name"]

    if op.type == "ACHAT":
        choose(all_actions, "k_achat_nom", "k_achat_nom_new", "k_achat_ticker_new")
        u["k_achat_qty"], u["k_achat_prix"] = float(op.quantity), float(op.price)
        u["k_achat_comm"] = float(op.commission or 0.0)
        u["k_achat_ttf"] = float(op.ttf) if op.ttf else None
        u["k_date_full"], u["k_heure_full"] = op.date, op.time
    elif op.type == "VENTE":
        choose(owned, "k_vente_nom", "k_vente_nom_new", "k_vente_ticker_new")
        u["k_vente_qty"], u["k_vente_prix"] = float(op.quantity), float(op.price)
        u["k_vente_comm"] = float((op.commission or 0.0) + (op.ttf or 0.0))
        u["k_date_full"], u["k_heure_full"] = op.date, op.time
    elif op.type == "DIVIDENDE":
        name = choose(owned, "k_div_nom", "k_div_nom_new", "k_div_ticker_new")
        if op.quantity is not None:
            u[f"k_div_qty__{name}" if name else "k_div_qty_new"] = float(op.quantity)
        u["k_div_montant"] = float(op.amount or 0.0)
        u["k_div_retenue"] = float(op.withholding) if op.withholding else None
        u["k_div_remb"] = float(op.capital_repayment) if op.capital_repayment else None
        u["k_date_simple"] = op.date
    elif op.type == "SPLIT":
        name = choose(owned, "k_split_nom", "k_split_nom_new", "k_split_ticker_new")
        if op.factor is not None:
            u["k_split_facteur" if name else "k_split_facteur_new"] = float(op.factor)
        u["k_date_simple"] = op.date
    elif op.type == "APPORT":
        u["k_apport_montant"], u["k_date_simple"] = float(op.amount), op.date
    elif op.type == "RETRAIT":
        u["k_retrait_montant"], u["k_date_simple"] = float(op.amount), op.date
    return u, known["name"]

def _import_apply(updates, pointer):
    """Callback du bouton « Pré-remplir » : s'exécute AVANT le rerun, donc avant la création des
    widgets — seul moment où Streamlit autorise à modifier leur valeur."""
    for k, v in updates.items():
        st.session_state[k] = v
    st.session_state["_imp_current"] = pointer

def _import_mark_done(op_type, final_name, final_ticker):
    """Appelé après l'enregistrement réussi d'une opération : coche l'opération importée et mémorise
    l'association « libellé du courtier → nom/ticker choisis » pour les prochains imports."""
    st.session_state["_imp_has_pending"] = False
    cur = st.session_state.pop("_imp_current", None)
    last = st.session_state.get("_imp_last")
    if not cur or not last or last["id"] != cur["doc"] or cur["type"] != op_type:
        return
    last["done"].add(cur["idx"])
    # Reste-t-il des opérations à saisir dans ce document ? Si oui, la fenêtre reste ouverte et
    # la liste se positionne sur la suivante.
    _restantes = [i for i in range(len(last["res"].ops)) if i not in last["done"]]
    if _restantes:
        st.session_state["_imp_has_pending"] = True
        st.session_state["_imp_next_idx"] = (last["id"][:8], _restantes[0])
    if op_type in ("ACHAT", "VENTE", "DIVIDENDE", "SPLIT") and final_name and cur.get("broker_name"):
        try:
            aliases = app_config.setdefault("import_aliases", {})
            aliases[di._norm(cur["broker_name"])] = {"nom": final_name, "ticker": final_ticker or ""}
            save_config(app_config)
        except Exception:
            pass

def _import_render_section():
    """Encart « Importer un document » tout en haut du formulaire."""
    if di is None:
        st.caption(f"📎 Import de documents indisponible ({_IMPORT_ERR}). Vérifiez que doc_import.py est à la racine du dépôt.")
        return
    last = st.session_state.get("_imp_last")
    with st.expander("📎 Importer un document (avis d'opéré, dividendes, virement, split…)", expanded=bool(last)):
        up = st.file_uploader("Document PDF du courtier", type=["pdf"], key="k_import_file",
                              label_visibility="collapsed")
        if up is not None:
            data = up.getvalue()
            doc_id = hashlib.sha1(data).hexdigest()
            if not last or last["id"] != doc_id:
                with st.spinner("Lecture du document…"):
                    res = di.parse_document(data)
                last = {"id": doc_id, "name": up.name, "data": data, "res": res, "done": set()}
                st.session_state["_imp_last"] = last
        if not last:
            st.caption("Reconnu automatiquement : avis d'opéré, relevé de coupons/dividendes, avis d'opération "
                       "sur titres (attribution gratuite), virements d'un relevé espèces (Boursorama). "
                       "Autres courtiers : analyse par IA si une clé ANTHROPIC_API_KEY est configurée.")
            return

        res = last["res"]
        c1, c2 = st.columns([4, 1])
        c1.caption(f"📄 {last['name']} — {res.doc_label}" + (" · analyse IA" if res.method == "ia" else ""))
        if c2.button("Oublier", key="k_import_forget", use_container_width=True):
            st.session_state.pop("_imp_last", None)
            st.session_state.pop("_imp_current", None)
            _rerun_scoped()
        for w in res.warnings:
            st.info(w)

        if not res.ops:
            key = _anthropic_key()
            if key and res.method != "ia":
                if st.button("🧠 Analyser avec l'IA", key="k_import_llm", use_container_width=True,
                             help="Envoie le texte du document (données personnelles retirées au mieux) à l'API Anthropic."):
                    with st.spinner("Analyse en cours…"):
                        last["res"] = di.parse_with_llm(last["data"], key, file_name=last["name"])
                    _rerun_scoped()
            elif not key:
                st.caption("Pour les documents d'autres courtiers : ajoutez ANTHROPIC_API_KEY dans les secrets Streamlit.")
            return

        ops = res.ops
        pending = [i for i in range(len(ops)) if i not in last["done"]]
        _nxt = st.session_state.pop("_imp_next_idx", None)
        if _nxt and _nxt[0] == last["id"][:8]:
            st.session_state[f"k_import_idx__{_nxt[0]}"] = _nxt[1]
        idx = st.selectbox(
            f"{len(ops)} opération(s) détectée(s)", list(range(len(ops))),
            index=pending[0] if pending else 0,
            format_func=lambda i: ("✅ " if i in last["done"] else "") + (ops[i].label or ops[i].type),
            key=f"k_import_idx__{last['id'][:8]}",
        )
        op = ops[idx]
        updates, known_name = _import_build_updates(op, _all_actions_historique_precalc, _actions_possedees_precalc)
        dup = di.find_duplicate(op, df_transactions, known_name)
        if dup:
            st.warning(f"⚠️ Une opération très proche est déjà enregistrée : {dup}.")
        if idx in last["done"]:
            st.caption("✅ Déjà saisie depuis ce document.")
        for n in op.notes:
            st.caption("• " + n)
        st.button("✨ Pré-remplir le formulaire", key="k_import_apply", type="primary", use_container_width=True,
                  on_click=_import_apply,
                  args=(updates, {"doc": last["id"], "idx": idx, "type": op.type, "broker_name": op.name}))

def _op_dialog_closed():
    """Appelé quand l'utilisateur ferme la fenêtre « Nouvelle opération » avec la croix."""
    st.session_state["_op_dialog_open"] = False

@dialog_wrapper("📝 Nouvelle opération", on_dismiss=_op_dialog_closed)
def dialog_saisie_operation():
    global df_transactions
    _import_render_section()
    st.caption("Sélectionnez un type d'opération pour afficher le formulaire correspondant.")
    op_type = st.selectbox(
        "Type d'opération", 
        ["ACHAT", "APPORT", "RETRAIT", "VENTE", "DIVIDENDE", "SPLIT"],
        key="k_op_type",
        index=None,
        placeholder="Choisissez un type d'opération...",
        format_func=lambda x: _OP_TYPE_LABELS.get(x, x),
        label_visibility="collapsed",
    )

    if op_type is not None:
        # Utilise les listes/dictionnaires précalculés une seule fois par exécution complète du
        # script (voir _actions_possedees_precalc et consorts plus haut), plutôt que de les
        # reconstruire à chaque interaction avec le formulaire (beaucoup plus rapide).
        actions_possedees = _actions_possedees_precalc
        all_actions_historique = _all_actions_historique_precalc
        ticker_by_name = _ticker_by_name_precalc
        qty_by_name = _qty_by_name_precalc

        nom_action, ticker = "", ""
        shares, price, commission, ttf = None, None, None, None
        montant_apport, montant_retrait, facteur_split, montant_dividende = None, None, None, None
        rompu_saisi = None
        rompu_date_saisie = None
        retenue_etrangere = None
        remboursement_capital = None
        arrondi_courtier = None

        # Liste remplie automatiquement par _req_field() avec la clé de chaque champ
        # obligatoire réellement affiché pour ce type d'opération (donc naturellement
        # différente selon ACHAT/VENTE/DIVIDENDE/SPLIT et selon "nouveau" ou "existant") ;
        # sert juste avant l'enregistrement à vérifier que rien d'obligatoire ne manque.
        required_fields = []

        if op_type == "ACHAT":
            _field_label("Nom de l'action / ETF")
            # UNE SEULE case : on choisit une action existante OU on tape directement un nouveau nom (proposé
            # dans la liste déroulante). Repli sur l'ancien fonctionnement (liste + case « Nouveau ») si la version
            # de Streamlit ne gère pas encore accept_new_options.
            _nom_achat_fusionne = True
            with _req_field("req_achat_nom", "k_achat_nom", track=required_fields):
                try:
                    choix_action_achat = st.selectbox(
                        "Nom de l'action / ETF",
                        options=all_actions_historique,
                        index=None,
                        accept_new_options=True,
                        placeholder="Choisissez une action existante ou tapez un nouveau nom...",
                        key="k_achat_nom",
                        label_visibility="collapsed",
                    )
                except TypeError:
                    _nom_achat_fusionne = False
                    choix_action_achat = st.selectbox(
                        "Nom de l'action / ETF",
                        options=[_SENTINEL_NOUVEAU] + all_actions_historique,
                        index=None,
                        placeholder="Choisissez une action existante ou ajoutez-en une nouvelle...",
                        key="k_achat_nom",
                        label_visibility="collapsed",
                    )
            _achat_nom_nouveau = (
                (choix_action_achat == _SENTINEL_NOUVEAU)
                or (_nom_achat_fusionne and bool(str(choix_action_achat or "").strip())
                    and choix_action_achat not in all_actions_historique)
            )
            if _achat_nom_nouveau:
                if choix_action_achat == _SENTINEL_NOUVEAU:
                    _field_label("Nom de l'action / ETF (Nouveau)")
                    with _req_field("req_achat_nom_nouveau", "k_achat_nom_new", track=required_fields):
                        nom_action = st.text_input("Nom de l'action / ETF (Nouveau)", key="k_achat_nom_new",
                                                    placeholder="Nom de l'action ou de l'ETF", label_visibility="collapsed")
                else:
                    nom_action = str(choix_action_achat).strip()
                _field_label("Ticker")
                with _req_field("req_achat_ticker_nouveau", "k_achat_ticker_new", track=required_fields):
                    ticker = st.text_input("Ticker", key="k_achat_ticker_new",
                                            placeholder="", label_visibility="collapsed").upper().strip()
            elif choix_action_achat is not None:
                nom_action = choix_action_achat
                match_t = df_transactions[df_transactions["Nom"] == nom_action]
                default_tick = match_t["Ticker"].iloc[-1] if not match_t.empty else ""
                _field_label("Ticker")
                k_tick = f"k_achat_ticker__{nom_action}"
                with _req_field("req_achat_ticker", k_tick, default=default_tick, track=required_fields):
                    ticker = st.text_input("Ticker", value=default_tick, key=k_tick,
                                            label_visibility="collapsed").upper().strip()
            else:
                nom_action, ticker = "", ""

            _field_label("Quantité")
            with _req_field("req_achat_qty", "k_achat_qty", track=required_fields):
                shares = st.number_input("Quantité", min_value=1.0, step=1.0, value=None, format="%.0f",
                                          key="k_achat_qty", placeholder="0", label_visibility="collapsed")
            _field_label("Prix unitaire (€)")
            with _req_field("req_achat_prix", "k_achat_prix", track=required_fields):
                price = st.number_input("Prix unitaire (€)", min_value=0.0, step=0.0001, value=None, format="%.4f",
                                         key="k_achat_prix", placeholder="0,0000", label_visibility="collapsed")
            _field_label("Commission (€)")
            with _req_field("req_achat_comm", "k_achat_comm", track=required_fields):
                commission = st.number_input("Commission (€)", min_value=0.0, step=0.01, value=None, format="%.2f",
                                              key="k_achat_comm", placeholder="0,00", label_visibility="collapsed")
            _field_label("TTF (€) — optionnel")
            ttf = st.number_input("TTF (€) — optionnel", min_value=0.0, step=0.01, value=None, format="%.2f",
                                   key="k_achat_ttf", placeholder="0,00", label_visibility="collapsed")

        elif op_type == "VENTE":
            _field_label("Nom de l'action / ETF")
            with _req_field("req_vente_nom", "k_vente_nom", track=required_fields):
                choix_action_vente = st.selectbox(
                    "Nom de l'action / ETF",
                    options=[_SENTINEL_NOUVEAU] + actions_possedees,
                    index=None,
                    placeholder="Choisissez une action possédée ou ajoutez-en une nouvelle...",
                    key="k_vente_nom",
                    label_visibility="collapsed",
                )
            if choix_action_vente == _SENTINEL_NOUVEAU:
                _field_label("Nom de l'action / ETF")
                with _req_field("req_vente_nom_nouveau", "k_vente_nom_new", track=required_fields):
                    nom_action = st.text_input("Nom de l'action / ETF", key="k_vente_nom_new",
                                                placeholder="Nom de l'action ou de l'ETF", label_visibility="collapsed")
                _field_label("Ticker")
                with _req_field("req_vente_ticker_nouveau", "k_vente_ticker_new", track=required_fields):
                    ticker = st.text_input("Ticker", key="k_vente_ticker_new",
                                            placeholder="", label_visibility="collapsed").upper().strip()
            elif choix_action_vente is not None:
                nom_action = choix_action_vente
                default_tick = ticker_by_name.get(nom_action, "")
                _field_label("Ticker")
                k_tick = f"k_vente_ticker__{nom_action}"
                with _req_field("req_vente_ticker", k_tick, default=default_tick, track=required_fields):
                    ticker = st.text_input("Ticker", value=default_tick, key=k_tick,
                                            label_visibility="collapsed").upper().strip()
            else:
                nom_action, ticker = "", ""

            _field_label("Quantité")
            with _req_field("req_vente_qty", "k_vente_qty", track=required_fields):
                shares = st.number_input("Quantité", min_value=1.0, step=1.0, value=None, format="%.0f",
                                          key="k_vente_qty", placeholder="0", label_visibility="collapsed")
            _field_label("Prix unitaire (€)")
            with _req_field("req_vente_prix", "k_vente_prix", track=required_fields):
                price = st.number_input("Prix unitaire (€)", min_value=0.0, step=0.0001, value=None, format="%.4f",
                                         key="k_vente_prix", placeholder="0,0000", label_visibility="collapsed")
            _field_label("Commission (€)")
            with _req_field("req_vente_comm", "k_vente_comm", track=required_fields):
                commission = st.number_input("Commission (€)", min_value=0.0, step=0.01, value=None, format="%.2f",
                                              key="k_vente_comm", placeholder="0,00", label_visibility="collapsed")
            # Pas de champ TTF pour une VENTE : la TTF française n'est due qu'à l'ACHAT de
            # titres éligibles, jamais lors d'une vente (voir aussi le simulateur, où la case
            # "Éligible TTF" n'apparaît elle aussi que pour un achat).
            ttf = 0.0

        elif op_type == "APPORT":
            _field_label("Montant (€)")
            with _req_field("req_apport_montant", "k_apport_montant", track=required_fields):
                montant_apport = st.number_input("Montant (€)", min_value=0.0, step=10.0, value=None, format="%.2f",
                                                  key="k_apport_montant", placeholder="0", label_visibility="collapsed")

        elif op_type == "RETRAIT":
            _field_label("Montant (€)")
            with _req_field("req_retrait_montant", "k_retrait_montant", track=required_fields):
                montant_retrait = st.number_input("Montant (€)", min_value=0.0, step=10.0, value=None, format="%.2f",
                                                   key="k_retrait_montant", placeholder="0", label_visibility="collapsed")

        elif op_type == "DIVIDENDE":
            _field_label("Nom de l'action / ETF")
            with _req_field("req_div_nom", "k_div_nom", track=required_fields):
                choix_action_div = st.selectbox(
                    "Nom de l'action / ETF",
                    options=[_SENTINEL_NOUVEAU] + actions_possedees,
                    index=None,
                    placeholder="Choisissez une action possédée ou ajoutez-en une nouvelle...",
                    key="k_div_nom",
                    label_visibility="collapsed",
                )
            if choix_action_div == _SENTINEL_NOUVEAU:
                _field_label("Nom de l'action / ETF")
                with _req_field("req_div_nom_nouveau", "k_div_nom_new", track=required_fields):
                    nom_action = st.text_input("Nom de l'action / ETF", key="k_div_nom_new",
                                                placeholder="Nom de l'action ou de l'ETF", label_visibility="collapsed")
                _field_label("Ticker")
                with _req_field("req_div_ticker_nouveau", "k_div_ticker_new", track=required_fields):
                    ticker = st.text_input("Ticker", key="k_div_ticker_new",
                                            placeholder="", label_visibility="collapsed").upper().strip()
                _field_label("Quantité")
                with _req_field("req_div_qty_nouveau", "k_div_qty_new", track=required_fields):
                    shares = st.number_input("Quantité", min_value=0.0, step=1.0, value=None, format="%.0f",
                                              key="k_div_qty_new", placeholder="0", label_visibility="collapsed")
            elif choix_action_div is not None:
                nom_action = choix_action_div
                default_tick = ticker_by_name.get(nom_action, "")
                default_qty = qty_by_name.get(nom_action, 1.0)
                _field_label("Ticker")
                k_tick = f"k_div_ticker__{nom_action}"
                with _req_field("req_div_ticker", k_tick, default=default_tick, track=required_fields):
                    ticker = st.text_input("Ticker", value=default_tick, key=k_tick,
                                            label_visibility="collapsed").upper().strip()
                _field_label("Quantité")
                k_qty = f"k_div_qty__{nom_action}"
                if k_qty not in st.session_state:
                    st.session_state[k_qty] = float(default_qty)
                with _req_field("req_div_qty", k_qty, default=float(default_qty)):
                    shares = st.number_input("Quantité", min_value=0.0, step=1.0, format="%.0f",
                                              key=k_qty, label_visibility="collapsed")
            else:
                nom_action, ticker = "", ""
                _field_label("Quantité")
                with _req_field("req_div_qty_vide", "k_div_qty_vide", track=required_fields):
                    shares = st.number_input("Quantité", min_value=0.0, step=1.0, value=None, format="%.0f",
                                              key="k_div_qty_vide", placeholder="0", label_visibility="collapsed")

            _field_label("Montant brut perçu (€)")
            with _req_field("req_div_montant", "k_div_montant", track=required_fields):
                montant_dividende = st.number_input("Montant brut perçu (€)", min_value=0.0, step=0.01, value=None, format="%.2f",
                                                     key="k_div_montant", placeholder="0,00", label_visibility="collapsed")
            _field_label("Retenue à la source (€) — optionnel")
            retenue_etrangere = st.number_input("Retenue à la source (€) — optionnel", min_value=0.0, step=0.01, value=None, format="%.2f",
                                                 key="k_div_retenue", placeholder="0,00", label_visibility="collapsed")
            _RB_CAPITAL_HELP = (
                "À renseigner uniquement si une partie de la distribution reçue n'est pas un dividende mais un "
                "remboursement de capital (ex. Schneider Electric). Ce montant est ajouté au cash perçu et "
                "vient réduire le PRU de la ligne, sans être compté comme un gain."
            )
            _field_label("Remboursement de capital inclus (€) — optionnel", help_text=_RB_CAPITAL_HELP)
            remboursement_capital = st.number_input(
                "Remboursement de capital inclus (€) — optionnel",
                min_value=0.0, step=0.01, value=None, format="%.2f",
                key="k_div_remb", placeholder="0,00", label_visibility="collapsed",
                help=_RB_CAPITAL_HELP
            )
            _ARRONDI_COURTIER_HELP = (
                "À renseigner lorsque le courtier applique un arrondi tel que Montant brut perçu − Retenue à "
                "la source ne tombe pas exactement sur le montant net réellement crédité sur le compte (petit "
                "écart de quelques centimes constaté sur le relevé). Indiquez ici l'écart, avec son signe, "
                "entre le montant net attendu (calculé) et le montant net réellement reçu : par exemple -0,01 "
                "si 0,01 € de moins que prévu a été crédité. Cette valeur est ajoutée au calcul pour retomber "
                "exactement sur le bon montant partout où il est utilisé (total des dividendes reçus, cash "
                "disponible...)."
            )
            _field_label("Arrondi du courtier (€) — optionnel", help_text=_ARRONDI_COURTIER_HELP)
            arrondi_courtier = st.number_input(
                "Arrondi du courtier (€) — optionnel",
                step=0.01, value=None, format="%.2f",
                key="k_div_arrondi", placeholder="0,00", label_visibility="collapsed",
                help=_ARRONDI_COURTIER_HELP
            )

        elif op_type == "SPLIT":
            _field_label("Nom de l'action / ETF")
            with _req_field("req_split_nom", "k_split_nom", track=required_fields):
                choix_action_split = st.selectbox(
                    "Nom de l'action / ETF",
                    options=[_SENTINEL_NOUVEAU] + actions_possedees,
                    index=None,
                    placeholder="Choisissez une action possédée ou ajoutez-en une nouvelle...",
                    key="k_split_nom",
                    label_visibility="collapsed",
                )
            if choix_action_split == _SENTINEL_NOUVEAU:
                _field_label("Nom de l'action / ETF")
                with _req_field("req_split_nom_nouveau", "k_split_nom_new", track=required_fields):
                    nom_action = st.text_input("Nom de l'action / ETF", key="k_split_nom_new",
                                                placeholder="Nom de l'action ou de l'ETF", label_visibility="collapsed")
                _field_label("Ticker")
                with _req_field("req_split_ticker_nouveau", "k_split_ticker_new", track=required_fields):
                    ticker = st.text_input("Ticker", key="k_split_ticker_new",
                                            placeholder="", label_visibility="collapsed").upper().strip()
                _field_label("Facteur de Split/Regroupement")
                with _req_field("req_split_facteur_nouveau", "k_split_facteur_new", track=required_fields):
                    facteur_split = st.number_input("Facteur de Split/Regroupement", min_value=0.0001, step=0.01, value=None, format="%.4f",
                                                     key="k_split_facteur_new", placeholder="0", label_visibility="collapsed")
            elif choix_action_split is not None:
                nom_action = choix_action_split
                default_tick = ticker_by_name.get(nom_action, "")
                default_qty = qty_by_name.get(nom_action, 1.1)
                _field_label("Ticker")
                k_tick = f"k_split_ticker__{nom_action}"
                with _req_field("req_split_ticker", k_tick, default=default_tick, track=required_fields):
                    ticker = st.text_input("Ticker", value=default_tick, key=k_tick,
                                            label_visibility="collapsed").upper().strip()
                _field_label("Facteur de Split/Regroupement")
                if "k_split_facteur" not in st.session_state or st.session_state["k_split_facteur"] is None:
                    st.session_state["k_split_facteur"] = float(default_qty)
                with _req_field("req_split_facteur", "k_split_facteur", track=required_fields):
                    facteur_split = st.number_input("Facteur de Split/Regroupement", min_value=0.0001, step=0.01, format="%.4f",
                                                     key="k_split_facteur", label_visibility="collapsed")
            else:
                nom_action, ticker = "", ""
                _field_label("Facteur de Split/Regroupement")
                with _req_field("req_split_facteur_vide", "k_split_facteur_vide", track=required_fields):
                    facteur_split = st.number_input("Facteur de Split/Regroupement", min_value=0.0001, step=0.01, value=None, format="%.4f",
                                                     key="k_split_facteur_vide", placeholder="0", label_visibility="collapsed")

            _field_label("Rompu versé en cash (€) — optionnel")
            rompu_saisi = st.number_input("Rompu versé en cash (€) — optionnel", min_value=0.0, step=0.001, value=None, format="%.3f",
                                           key="k_split_rompu", placeholder="0,000", label_visibility="collapsed")

            _field_label("Date de versement des rompus, si différente de la date du split — optionnel")
            _rompu_date_current = st.session_state.get("k_split_rompu_date")
            _rompu_date_requise = bool(rompu_saisi) and rompu_saisi > 0 and (_rompu_date_current is None or _rompu_date_current == "")
            with (st.container(key="req_split_rompu_date") if _rompu_date_requise else contextlib.nullcontext()):
                rompu_date_saisie = st.date_input(
                    "Date de versement des rompus", value=None, format="DD-MM-YYYY",
                    key="k_split_rompu_date", label_visibility="collapsed",
                )

        st.markdown('<div class="op-card-title">🗓️ Date de l\'opération</div>', unsafe_allow_html=True)
        # Cases date/heure vides par défaut : on masque le format indicatif (« DD-MM-YYYY », « HH:mm:ss »).
        st.markdown(
            "<style>"
            ".st-key-k_date_full input::placeholder, .st-key-k_date_simple input::placeholder, "
            ".st-key-k_heure_full input::placeholder { color: transparent !important; opacity: 0 !important; } "
            ".st-key-k_heure_full [data-baseweb=\"select\"] [class*=\"laceholder\"], "
            ".st-key-k_heure_full [data-baseweb=\"select\"] div[aria-hidden=\"true\"] { color: transparent !important; } "
            "</style>",
            unsafe_allow_html=True,
        )
        if op_type in ["APPORT", "RETRAIT", "DIVIDENDE", "SPLIT"]:
            with _req_field("req_date_simple", "k_date_simple", track=required_fields):
                tx_date = st.date_input("Date", value=None, format="DD-MM-YYYY", key="k_date_simple", label_visibility="collapsed")
            tx_time = time(0, 0, 0)
        else:
            col_d1, col_d2 = st.columns(2)
            with col_d1:
                _field_label("Date")
                with _req_field("req_date_full", "k_date_full", track=required_fields):
                    tx_date = st.date_input("Date", value=None, format="DD-MM-YYYY", key="k_date_full", label_visibility="collapsed")
            with col_d2:
                _field_label("Heure")
                with _req_field("req_heure_full", "k_heure_full", track=required_fields):
                    tx_time = st.time_input("Heure", value=None, step=1, key="k_heure_full", label_visibility="collapsed")

        # Les champs numériques vides (None) sont ramenés à 0.0 juste avant l'enregistrement,
        # pour ne jamais planter un calcul en aval — mais restent bien vides à l'écran tant
        # que l'utilisateur n'a rien saisi. Idem pour la date/l'heure, non présélectionnées :
        # si elles n'ont pas été touchées, on retombe sur aujourd'hui / midi au moment d'enregistrer.
        shares = shares if shares is not None else 0.0
        price = price if price is not None else 0.0
        commission = commission if commission is not None else 0.0
        ttf = ttf if ttf is not None else 0.0
        montant_apport = montant_apport if montant_apport is not None else 0.0
        montant_retrait = montant_retrait if montant_retrait is not None else 0.0
        facteur_split = facteur_split if facteur_split is not None else 0.0
        montant_dividende = montant_dividende if montant_dividende is not None else 0.0
        rompu_saisi = rompu_saisi if rompu_saisi is not None else 0.0
        retenue_etrangere = retenue_etrangere if retenue_etrangere is not None else 0.0
        remboursement_capital = remboursement_capital if remboursement_capital is not None else 0.0
        arrondi_courtier = arrondi_courtier if arrondi_courtier is not None else 0.0
        tx_date = tx_date if tx_date is not None else _today_paris().date()
        tx_time = tx_time if tx_time is not None else time(12, 0, 0)

        st.markdown('<div style="margin-top: 6px;"></div>', unsafe_allow_html=True)
        if st.button("💾  Enregistrer l'opération", type="primary", use_container_width=True):
            missing_fields = [k for k in required_fields if st.session_state.get(k) in (None, "")]
            if missing_fields:
                st.error("⚠️ Impossible d'enregistrer l'opération : tous les champs obligatoires (encadrés en rouge) ne sont pas renseignés.")
            else:
                try:
                    full_dt = datetime.combine(tx_date, tx_time)

                    # L'ancienne alerte TTF "même jour", déclenchée uniquement au moment de
                    # l'enregistrement d'une vente, a été remplacée par une détection automatique
                    # de toutes les anomalies TTF (voir detect_ttf_anomalies_cached plus bas) :
                    # elle s'applique à CHAQUE rechargement de l'app, sur TOUT l'historique, et
                    # couvre donc aussi bien cette nouvelle opération que les transactions déjà
                    # présentes — plus besoin de la déclencher ici au cas par cas.

                    if op_type == "APPORT":
                        s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = "Compte Courant", "APPORT", montant_apport, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
                    elif op_type == "RETRAIT":
                        s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = "Compte Courant", "RETRAIT", montant_retrait, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
                    elif op_type == "SPLIT":
                        s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = nom_action, ticker, facteur_split, 0.0, 0.0, 0.0, rompu_saisi, 0.0, 0.0, 0.0
                    elif op_type == "DIVIDENDE":
                        s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = nom_action, ticker, shares, montant_dividende, 0.0, 0.0, 0.0, retenue_etrangere, remboursement_capital, arrondi_courtier
                    else:
                        s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = nom_action, ticker, shares, price, commission, ttf, 0.0, 0.0, 0.0, 0.0

                    # Date de versement des rompus : si l'utilisateur n'a pas précisé de date
                    # différente, on retombe sur la date du split lui-même (comportement
                    # historique, strictement identique pour les SPLIT sans rompu ou sans date
                    # de versement distincte renseignée).
                    s_date_rompus = datetime.combine(rompu_date_saisie, time(0, 0, 0)) if (op_type == "SPLIT" and rompu_date_saisie is not None) else full_dt

                    frais_tot_calc = s_comm + s_ttf + s_ret if op_type == "DIVIDENDE" else s_comm + s_ttf

                    new_row = pd.DataFrame({
                        "Date_Heure": [full_dt], "Type": [op_type], "Nom": [s_nom], "Ticker": [s_tick],
                        "Quantité": [s_qty], "Prix Unitaire (€)": [s_pr], "Commission (€)": [s_comm],
                        "TTF (€)": [s_ttf], "Frais Totaux (€)": [frais_tot_calc], "Rompu": [s_rompu],
                        "Retenue_Source_Etrangere": [s_ret], "Remboursement_Capital": [s_remb],
                        "Arrondi_Courtier": [s_arrondi], "Date_Rompus": [s_date_rompus]
                    })
                    df_transactions = pd.concat([df_transactions, new_row], ignore_index=True)
                    ok_save, err_save = save_transactions_csv(df_transactions)
                    if ok_save:
                        # load_data.clear() : indispensable en plus du st.rerun(). load_data()
                        # est mise en cache indéfiniment (ttl=None) tant qu'elle n'est pas vidée
                        # explicitement ; sans ce clear(), le cache renverrait l'ancienne version
                        # au lieu de relire les données fraîchement enregistrées dans Supabase — l'appli
                        # a l'air de "ne rien faire" alors que le fichier est bien à jour sur disque.
                        load_data.clear()
                        _import_mark_done(op_type, s_nom, s_tick)
                        # La fenêtre se referme après l'enregistrement, sauf s'il reste des opérations
                        # à saisir dans le document importé (ex. relevé de dividendes à plusieurs lignes).
                        if not st.session_state.get("_imp_has_pending"):
                            st.session_state["_op_dialog_open"] = False
                        st.toast("✅ Opération enregistrée avec succès !", icon="✅")
                        st.rerun()
                    else:
                        st.error(err_save)
                except Exception as e:
                    st.error(f"Erreur : {e}")

def _sim_headline_duo(items):
    """Deux indicateurs côte à côte (y compris sur téléphone) ; items = (libellé, valeur, sous-texte, mis_en_avant)."""
    parts = []
    for it in items:
        k, v, sub, hl = it[:4]
        col = it[4] if len(it) > 4 else None
        sty = f' style="color:{col};"' if col else ""
        parts.append(
            f'<div class="pea-duo-item{" hl" if hl else ""}"><div class="k">{k}</div><div class="v"{sty}>{v}</div>'
            + (f'<div class="s">{sub}</div>' if sub else "") + "</div>"
        )
    cls = " tri" if len(items) == 3 else ""
    st.markdown(f'<div class="pea-duo{cls}">{"".join(parts)}</div>', unsafe_allow_html=True)


def _sim_headline(label, value, sub="", color="#0f172a"):
    sub_html = f'<div class="s">{sub}</div>' if sub else ""
    st.markdown(
        f'<div class="pea-head"><div class="k">{label}</div><div class="v" style="color:{color};">{value}</div>{sub_html}</div>',
        unsafe_allow_html=True,
    )


@dialog_wrapper("🧪 Simulation nouvelle opération")
def dialog_simulation_operation():
    """Simulateur "what-if" (Achat / Vente / Split) : ne modifie jamais les transactions
    réelles. Affiche directement dans cette même fenêtre modale le nouveau cash disponible
    et le nouveau PRU de la ligne compte tenu des frais, exactement comme le ferait
    l'opération réelle équivalente."""
 
    # Taux de commission courtier et taux de TTF en vigueur : affichés et modifiables ici, en
    # haut de la pop-up, pré-remplis avec la dernière valeur utilisée (persistée dans la
    # configuration de l'app) plutôt que ressaisis à chaque simulation. Toute modification ici
    # met à jour la même configuration que le réglage "💳 Commission courtier (%)" du haut du
    # dashboard : les deux emplacements restent donc synchronisés.
    col_taux_courtier_wi, col_taux_ttf_wi = st.columns(2)
    with col_taux_courtier_wi:
        _taux_courtier_cfg = float(app_config.get("frais_courtier_pct", 0.5))
        taux_courtier_pct_wi = st.number_input(
            "💳 Commission courtier (%)",
            min_value=0.0, max_value=10.0, step=0.01,
            value=_taux_courtier_cfg, format="%.2f",
            key="k_whatif_taux_courtier_pct",
            help="Taux de commission prélevé par votre courtier (% du montant de l'opération), modifiable au centième de pourcent près. Pré-rempli avec la dernière valeur utilisée."
        )
        if taux_courtier_pct_wi != _taux_courtier_cfg:
            app_config["frais_courtier_pct"] = float(taux_courtier_pct_wi)
            _ok_cfg_wi_c, _err_cfg_wi_c = save_config(app_config)
            if not _ok_cfg_wi_c:
                st.warning(_err_cfg_wi_c)
    with col_taux_ttf_wi:
        _taux_ttf_cfg = float(app_config.get("taux_ttf_pct", 0.4))
        taux_ttf_pct_wi = st.number_input(
            "🏛️ Taux TTF (%)",
            min_value=0.0, max_value=10.0, step=0.01,
            value=_taux_ttf_cfg, format="%.2f",
            key="k_whatif_taux_ttf_pct",
            help="Taux de la taxe sur les transactions financières actuellement en vigueur, modifiable au centième de pourcent près. Pré-rempli avec la dernière valeur utilisée."
        )
        if taux_ttf_pct_wi != _taux_ttf_cfg:
            app_config["taux_ttf_pct"] = float(taux_ttf_pct_wi)
            _ok_cfg_wi_t, _err_cfg_wi_t = save_config(app_config)
            if not _ok_cfg_wi_t:
                st.warning(_err_cfg_wi_t)
    st.markdown("<hr style='margin:10px 0;'>", unsafe_allow_html=True)

    def _delta_eur(delta_val):
        color = "#16a34a" if delta_val > 0.005 else ("#dc2626" if delta_val < -0.005 else "#64748b")
        if delta_val > 0.005:
            return "▲ +" + fmt_eur(delta_val), color
        if delta_val < -0.005:
            return "▼ " + fmt_eur(delta_val), color
        return "▬ " + fmt_eur(0.0), color

    def _delta_prix(delta_val):
        color = "#16a34a" if delta_val > 0.00005 else ("#dc2626" if delta_val < -0.00005 else "#64748b")
        if delta_val > 0.00005:
            return "▲ +" + fmt_price_dynamic(delta_val, include_comm=False), color
        if delta_val < -0.00005:
            return "▼ " + fmt_price_dynamic(delta_val, include_comm=False), color
        return "▬ " + fmt_price_dynamic(0.0, include_comm=False), color

    def _delta_pct(delta_val):
        color = "#16a34a" if delta_val > 0.005 else ("#dc2626" if delta_val < -0.005 else "#64748b")
        if delta_val > 0.005:
            return f"▲ +{delta_val:,.2f} %".replace(",", " ").replace(".", ","), color
        if delta_val < -0.005:
            return f"▼ {delta_val:,.2f} %".replace(",", " ").replace(".", ","), color
        return "▬ 0,00 %", color

    def _render_before_after(items):
        cards = ""
        for label, avant_str, apres_str, delta_str, delta_color in items:
            _acc = delta_color if (isinstance(delta_color, str) and delta_color.startswith("#")) else "#94a3b8"
            _pill_bg = (_acc + "1a") if len(_acc) == 7 else "#f1f5f9"
            cards += (
                f'<div style="background:linear-gradient(180deg,#ffffff,#f8fafc); border:1px solid #e2e8f0; border-top:3px solid {_acc}; '
                'border-radius:12px; padding:12px 14px; flex:1 1 150px; min-width:0; box-shadow:0 1px 3px rgba(15,23,42,0.06);">'
                f'<div style="font-size:0.7rem; color:#475569; text-transform:uppercase; font-weight:800; letter-spacing:0.05em; margin-bottom:10px;">{label}</div>'
                '<div style="display:flex; align-items:flex-end; gap:10px; flex-wrap:wrap;">'
                '<div><div style="font-size:0.6rem; color:#94a3b8; font-weight:700; text-transform:uppercase;">Avant</div>'
                f'<div style="font-size:0.9rem; color:#64748b; font-weight:600;">{avant_str}</div></div>'
                '<div style="color:#94a3b8; font-weight:800; font-size:1.1rem; padding-bottom:1px;">→</div>'
                '<div><div style="font-size:0.6rem; color:#94a3b8; font-weight:700; text-transform:uppercase;">Après</div>'
                f'<div style="font-size:1.2rem; font-weight:800; color:#0f172a; line-height:1.15;">{apres_str}</div></div>'
                '</div>'
                f'<div style="display:inline-block; margin-top:10px; padding:2px 10px; border-radius:999px; background:{_pill_bg}; '
                f'font-size:0.76rem; font-weight:800; color:{_acc};">{delta_str}</div>'
                '</div>'
            )
        st.markdown(f'<div style="display:flex; flex-wrap:wrap; gap:10px;">{cards}</div>', unsafe_allow_html=True)

    type_wi = st.radio("Type d'opération", ["Achat", "Vente", "Achat/Vente", "Split"], horizontal=True, key="k_whatif_type")

    df_port_actif_wi = df_port[df_port["Quantité"] > 0.0001].copy() if not df_port.empty else df_port

    pos_existante = None
    nom_wi, ticker_wi = None, None

    if type_wi == "Achat":
        noms_dispo_wi = ["➕ Nouvelle valeur..."] + sorted(df_port["Nom"].dropna().unique().tolist()) if not df_port.empty else ["➕ Nouvelle valeur..."]
        choix_wi = st.selectbox("Valeur concernée", noms_dispo_wi, key="k_whatif_choix_achat")
        if choix_wi == "➕ Nouvelle valeur...":
            # Les champs Ticker / Nom de la valeur ne sont volontairement PAS demandés ici : la
            # simulation ne va de toute façon jamais chercher un cours en direct pour une valeur
            # non détenue (elle repose uniquement sur le prix unitaire saisi par l'utilisateur
            # juste après), donc les faire remplir n'apporterait rien et obligerait l'opérateur à
            # aller chercher inutilement le ticker exact d'une valeur qu'il ne compte pas
            # forcément enregistrer pour de vrai.
            nom_wi = "Nouvelle valeur"
            ticker_wi = ""
        else:
            nom_wi = choix_wi
            _match_wi = df_port[df_port["Nom"] == choix_wi]
            if not _match_wi.empty:
                pos_existante = _match_wi.iloc[0]
                ticker_wi = pos_existante["Ticker"]
    elif type_wi in ("Vente", "Split"):
        # Vente ET Split partagent la même sélection (choisir une position détenue) : c'est
        # le comportement d'origine, préservé tel quel. "Achat/Vente" n'a besoin d'aucune
        # sélection de position (voir plus bas) : c'est une simulation autonome d'aller-retour
        # achat puis revente, indépendante des positions déjà en portefeuille.
        if df_port_actif_wi.empty:
            st.info("Aucune position en portefeuille pour lancer cette simulation.")
        else:
            noms_dispo_wi = sorted(df_port_actif_wi["Nom"].dropna().unique().tolist())
            choix_wi = st.selectbox("Valeur concernée", noms_dispo_wi, key="k_whatif_choix_vente")
            nom_wi = choix_wi
            _match_wi = df_port_actif_wi[df_port_actif_wi["Nom"] == choix_wi]
            if not _match_wi.empty:
                pos_existante = _match_wi.iloc[0]
                ticker_wi = pos_existante["Ticker"]

    if type_wi in ("Achat", "Vente"):
        # Comme dans "Nouvelle opération" : le titre du champ est affiché séparément, AVANT
        # l'encadré rouge (_field_label, avec label_visibility="collapsed" sur le widget
        # lui-même), pour que le liseret rouge tant que le champ est vide n'entoure QUE le champ
        # chiffrable et jamais son intitulé.
        # Le nombre de titres déjà détenus (pour une vente) ou le PRU actuel de la position
        # (les deux quand la valeur est déjà en portefeuille) sont rappelés entre parenthèses
        # à côté des libellés, pour ne pas avoir à quitter la simulation pour les retrouver.
        _qte_detenue_label_wi = (
            f"Quantité (Nombre détenu dans le portefeuille : {float(pos_existante['Quantité']):g})"
            if pos_existante is not None else "Quantité"
        )
        _field_label(_qte_detenue_label_wi)
        with _req_field("req_whatif_qte", "k_whatif_qte", track=None):
            qte_wi = st.number_input("Quantité", min_value=0.0, step=1.0, value=None, format="%.0f",
                                      placeholder="0", key="k_whatif_qte", label_visibility="collapsed")
        qte_wi = qte_wi if qte_wi is not None else 0.0
        prix_defaut_wi = float(pos_existante["Prix Actuel (€)"]) if (pos_existante is not None and float(pos_existante["Prix Actuel (€)"]) > 0) else None
        # Pour un achat, on saisit un prix d'achat (le libellé "estimé" n'avait pas lieu d'être
        # puisque c'est le prix auquel on compte réellement acheter) ; pour une vente, le libellé
        # d'origine est conservé.
        _prix_label_base_wi = "Prix d'achat (€)" if type_wi == "Achat" else "Prix de vente (€)"
        _prix_label_wi = (
            f"{_prix_label_base_wi} (PRU actuel : {fmt_price_dynamic(float(pos_existante['PRU Net (€)']), include_comm=False)})"
            if pos_existante is not None else _prix_label_base_wi
        )
        _field_label(_prix_label_wi)
        with _req_field("req_whatif_prix", "k_whatif_prix", default=prix_defaut_wi, track=None):
            prix_wi = st.number_input(_prix_label_base_wi, min_value=0.0, step=0.0001, format="%.4f",
                                       value=prix_defaut_wi, placeholder="0,0000", key="k_whatif_prix", label_visibility="collapsed")
        prix_wi = prix_wi if prix_wi is not None else 0.0

        # La commission courtier n'est plus un champ € éditable : elle est systématiquement
        # calculée à partir du taux "💳 Commission courtier (%)" renseigné en haut de la fenêtre
        # (sauf exonération cochée ci-dessous), puisqu'elle sera de toute façon toujours utilisée
        # telle quelle. Idem pour la TTF, toujours calculée à partir du taux "🏛️ Taux TTF (%)"
        # quand la case "Éligible TTF" est cochée. Plus aucune ressaisie manuelle en euros.
        _taux_courtier_wi = taux_courtier_pct_wi / 100.0
        montant_op_brut_wi = round(qte_wi * prix_wi, 2)

        # La case "Éligible TTF" ne concerne que les ACHATS : la TTF française est due lors de
        # l'acquisition de titres éligibles, jamais lors d'une vente ou d'un split.
        # "Exonération des commissions courtier" concerne en revanche aussi bien l'achat que la
        # vente (ex. offre de courtage gratuit sous conditions) : quand elle est cochée, le taux
        # de commission renseigné en % n'est pas appliqué, quel que soit le sens de l'opération.
        eligible_ttf_wi = False
        if type_wi == "Achat":
            eligible_ttf_wi = st.checkbox(
                "☑️ Éligible TTF (taxe sur les transactions financières)",
                key="k_whatif_eligible_ttf",
                help="À cocher si la valeur simulée est soumise à la TTF française : le taux renseigné en % ne sera alors pas appliqué."
            )
        exoneration_commission_wi = st.checkbox(
            "🚫 Exonération des commissions courtier",
            key="k_whatif_exoneration_commission",
            help="À cocher si cette opération est exonérée de commission courtier : le taux renseigné en % ne sera alors pas appliqué."
        )

        commission_wi = 0.0 if exoneration_commission_wi else round(montant_op_brut_wi * _taux_courtier_wi, 2)
        ttf_wi = round(montant_op_brut_wi * (taux_ttf_pct_wi / 100.0), 2) if eligible_ttf_wi else 0.0

        frais_wi = round(commission_wi + ttf_wi, 2)
        montant_total_wi = round(montant_op_brut_wi + frais_wi, 2) if type_wi == "Achat" else round(montant_op_brut_wi - frais_wi, 2)
        _detail_frais_wi = []
        if commission_wi > 0:
            _detail_frais_wi.append(f"commission {fmt_eur(commission_wi)}")
        elif exoneration_commission_wi:
            _detail_frais_wi.append("commission exonérée")
        if ttf_wi > 0:
            _detail_frais_wi.append(f"TTF {fmt_eur(ttf_wi)}")
        _detail_frais_str_wi = " + ".join(_detail_frais_wi) if _detail_frais_wi else "aucun frais"
        # Prix unitaire net de frais de l'opération : pour un achat, les frais s'ajoutent au
        # prix payé (on paie plus cher que le prix affiché) ; pour une vente, ils se retranchent
        # du prix perçu (on touche moins que le prix affiché). Recalculé directement à partir du
        # montant total déjà connu (montant_total_wi) plutôt que reconstruit indépendamment, pour
        # ne jamais diverger de celui-ci.
        prix_net_wi = (montant_total_wi / qte_wi) if qte_wi > 0 else 0.0
        _label_net_wi = "Prix d'achat par action net de frais" if type_wi == "Achat" else "Prix de vente par action net de frais"
        _acc_op = "#0284c7" if type_wi == "Achat" else "#7c3aed"
        _bg_op = "linear-gradient(135deg,#f0f9ff,#e0f2fe)" if type_wi == "Achat" else "linear-gradient(135deg,#f5f3ff,#ede9fe)"
        _bd_op = "#bae6fd" if type_wi == "Achat" else "#c4b5fd"
        st.markdown(
            f'<div style="background:{_bg_op}; border:1px solid {_bd_op}; border-left:5px solid {_acc_op}; border-radius:12px; '
            f'padding:14px 18px; margin-top:6px; box-shadow:0 2px 8px rgba(15,23,42,0.06);">'
            f'<div style="display:flex; justify-content:space-between; align-items:center; flex-wrap:wrap; gap:10px;">'
            f'<div><div style="font-size:0.7rem; color:{_acc_op}; text-transform:uppercase; font-weight:800; letter-spacing:0.06em;">'
            f'{"🛒" if type_wi == "Achat" else "📤"} Montant de l\'opération</div>'
            f'<div style="font-size:0.82rem; color:#475569; margin-top:4px;">{qte_wi:g} × {fmt_eur(prix_wi)}</div>'
            f'<div style="font-size:0.74rem; color:#64748b; margin-top:2px;">{_detail_frais_str_wi}</div></div>'
            f'<div style="text-align:right;"><div style="font-size:0.7rem; color:#64748b; text-transform:uppercase; font-weight:700; letter-spacing:0.05em;">'
            f'Total {"payé" if type_wi == "Achat" else "perçu"}</div>'
            f'<div style="font-size:1.55rem; font-weight:800; color:{_acc_op}; line-height:1.15;">{fmt_eur(montant_total_wi)}</div></div></div>'
            f'<div style="margin-top:10px; padding-top:8px; border-top:1px dashed {_bd_op}; font-size:0.8rem; color:#475569;">'
            f'💶 {_label_net_wi} : <b style="color:#0f172a;">{fmt_price_dynamic(prix_net_wi, include_comm=False)}</b></div>'
            f'</div>',
            unsafe_allow_html=True
        )

        st.markdown("<hr style='margin:14px 0;'>", unsafe_allow_html=True)

        if not nom_wi or qte_wi <= 0 or prix_wi <= 0:
            st.markdown(
                '<div style="padding: 20px; background:#f8fafc; border:1px dashed #cbd5e1; border-radius:12px; text-align:center; color:#64748b;">'
                '<div style="font-size:1.4rem;">🧪</div>'
                '<div style="font-size:0.88rem; font-weight:600; margin-top:6px;">Renseignez une valeur, une quantité et un prix pour lancer la simulation</div></div>',
                unsafe_allow_html=True
            )
        else:
            qte_avant = float(pos_existante["Quantité"]) if pos_existante is not None else 0.0
            invested_avant = float(pos_existante["Capital Investi (€)"]) if pos_existante is not None else 0.0
            pru_avant = float(pos_existante["PRU Net (€)"]) if pos_existante is not None else 0.0
            valeur_pos_avant = float(pos_existante["Valeur Actuelle (€)"]) if pos_existante is not None else 0.0

            # Poche espèces actuelle, calculée localement (plutôt que réutilisée depuis le
            # script principal) : ce dialogue peut s'ouvrir AVANT que le script principal n'ait
            # lui-même calculé "poche_especes" plus bas (le bouton d'ouverture est placé tôt
            # exprès, pour que la fenêtre s'ouvre instantanément sans attendre les calculs
            # coûteux). get_portfolio_history est mise en cache (st.cache_data) : cet appel
            # retombe donc sur le cache déjà chaud dans l'immense majorité des cas.
            _history_wi = get_portfolio_history(df_transactions)
            cash_avant = 0.0
            if _history_wi is not None and not _history_wi.empty:
                cash_avant = _history_wi["Poche Espèces (€)"].iloc[-1]

            montant_op = qte_wi * prix_wi
            gain_realise_op = None

            if type_wi == "Achat":
                if montant_op + frais_wi > cash_avant:
                    st.warning(f"⚠️ Ce montant ({fmt_eur(montant_op + frais_wi)}) dépasse la poche espèces disponible ({fmt_eur(cash_avant)}) — la simulation suppose malgré tout que le versement est disponible.")
                cash_apres = cash_avant - montant_op - frais_wi
                qte_apres = qte_avant + qte_wi
                invested_apres = invested_avant + montant_op + frais_wi
                pru_apres = invested_apres / qte_apres if qte_apres > 0.0001 else 0.0
            else:
                if qte_wi > qte_avant:
                    st.error(f"⚠️ Vous ne détenez que {qte_avant:g} unité(s) de {nom_wi} — impossible de simuler une vente de {qte_wi:g}.")
                qte_vendue_effective = min(qte_wi, qte_avant)
                cost_basis_sold = qte_vendue_effective * pru_avant
                gain_realise_op = montant_op - frais_wi - cost_basis_sold
                cash_apres = cash_avant + montant_op - frais_wi
                qte_apres = max(0.0, qte_avant - qte_wi)
                invested_apres = qte_apres * pru_avant
                pru_apres = pru_avant

            # Valeur totale du portefeuille avant/après : sert uniquement au calcul du poids de
            # la ligne ci-dessous (elle-même affichée), la carte "Valeur totale du portefeuille"
            # ayant été retirée de l'affichage au profit du "Montant de l'opération" plus haut.
            valeur_totale_avant = tot_value_actions + cash_avant
            valeur_pos_apres = qte_apres * prix_wi
            valeur_totale_apres = valeur_totale_avant - frais_wi
            gain_latent_avant = valeur_pos_avant - invested_avant
            gain_latent_apres = valeur_pos_apres - invested_apres
            poids_avant = (valeur_pos_avant / valeur_totale_avant * 100) if valeur_totale_avant > 0 else 0.0
            poids_apres = (valeur_pos_apres / valeur_totale_apres * 100) if valeur_totale_apres > 0 else 0.0

            if gain_realise_op is not None:
                gr_color = "#16a34a" if gain_realise_op >= 0 else "#dc2626"
                gr_icon = "📈" if gain_realise_op >= 0 else "📉"
                # % réalisé sur cette vente = gain / coût d'acquisition des titres vendus (et
                # non sur le montant brut de la vente), cohérent avec la "Performance (%)"
                # affichée ailleurs dans l'app pour une position en portefeuille.
                gr_pct = (gain_realise_op / cost_basis_sold * 100) if cost_basis_sold > 0 else 0.0
                gr_pct_str = f"{_arrow_sym(gr_pct)} {'+' if gr_pct >= 0 else ''}{gr_pct:,.2f} %".replace(".", ",")
                st.markdown(
                    f'<div style="margin-bottom: 12px; padding: 12px 16px; background:#f8fafc; border:1px solid #e2e8f0; border-left: 4px solid {gr_color}; border-radius:8px;">'
                    f'<div style="font-size:0.78rem; color:#64748b; text-transform:uppercase; font-weight:700; letter-spacing:0.04em;">{gr_icon} Plus-value réalisée par cette vente</div>'
                    f'<div style="display:flex; align-items:baseline; gap:10px;">'
                    f'<div style="font-size:1.35rem; font-weight:800; color:{gr_color}; margin-top:2px;">{fmt_eur(gain_realise_op)}</div>'
                    f'<div style="font-size:1rem; font-weight:700; color:{gr_color};">({gr_pct_str})</div>'
                    f'</div></div>',
                    unsafe_allow_html=True
                )

            d_cash, c_cash = _delta_eur(cash_apres - cash_avant)
            d_qte = qte_apres - qte_avant
            d_qte_color = "#16a34a" if d_qte > 0 else ("#dc2626" if d_qte < 0 else "#64748b")
            d_qte_str = f"{_arrow_sym(d_qte, 1e-9)} {'+' if d_qte > 0 else ''}{d_qte:g} titre(s)"
            d_pru, c_pru = _delta_prix(pru_apres - pru_avant)
            d_valpos, c_valpos = _delta_eur(valeur_pos_apres - valeur_pos_avant)
            d_gainlat, c_gainlat = _delta_eur(gain_latent_apres - gain_latent_avant)
            d_poids, c_poids = _delta_pct(poids_apres - poids_avant)

            _cartes_ligne1_wi = [
                ("💰 Poche espèces", fmt_eur(cash_avant), fmt_eur(cash_apres), d_cash, c_cash),
                ("📦 Quantité détenue", f"{qte_avant:g}", f"{qte_apres:g}", d_qte_str, d_qte_color),
            ]
            if type_wi == "Achat":
                # Le PRU net n'évolue jamais lors d'une simple vente (seule la quantité détenue
                # change) : la carte n'a donc de sens à afficher que côté achat.
                _cartes_ligne1_wi.append(("🎯 PRU net", fmt_price_dynamic(pru_avant, include_comm=False), fmt_price_dynamic(pru_apres, include_comm=False), d_pru, c_pru))
            _render_before_after(_cartes_ligne1_wi)
            st.markdown("<div style='height:10px;'></div>", unsafe_allow_html=True)
            _render_before_after([
                ("📊 Valeur de la ligne", fmt_eur(valeur_pos_avant), fmt_eur(valeur_pos_apres), d_valpos, c_valpos),
                ("💹 Gain latent sur la ligne", fmt_eur(gain_latent_avant), fmt_eur(gain_latent_apres), d_gainlat, c_gainlat),
                ("⚖️ Poids dans le portefeuille", f"{poids_avant:,.2f} %".replace(".", ","), f"{poids_apres:,.2f} %".replace(".", ","), d_poids, c_poids),
            ])

            # --- Transfert de la simulation vers une VRAIE opération ---
            # Si la simulation est cohérente, un clic ouvre « Nouvelle opération » déjà pré-remplie
            # (type, valeur, quantité, prix, commission et, pour un achat, TTF) : il ne reste plus
            # qu'à saisir la date et l'heure réelles de la transaction. Une vente supérieure au
            # nombre de titres détenus n'est pas transférable (la simulation affiche déjà l'erreur).
            _transfert_possible = (type_wi == "Achat") or (qte_wi <= qte_avant + 1e-9)
            if _transfert_possible:
                st.markdown("<hr style='margin:14px 0;'>", unsafe_allow_html=True)
                st.caption(
                    "La simulation vous semble cohérente ? Transférez-la vers une vraie "
                    + ("opération d'achat" if type_wi == "Achat" else "opération de vente")
                    + " : quantité, prix, commission"
                    + (" et TTF" if type_wi == "Achat" else "")
                    + " seront déjà renseignés, il ne restera qu'à saisir la date et l'heure."
                )
                if st.button(
                    "➡️ Transférer vers une vraie " + ("opération d'achat" if type_wi == "Achat" else "opération de vente"),
                    key="btn_whatif_transfer", type="primary", use_container_width=True,
                ):
                    _ss_tr = st.session_state
                    _op_tr = "ACHAT" if type_wi == "Achat" else "VENTE"
                    _pre_tr = "k_achat" if _op_tr == "ACHAT" else "k_vente"
                    _noms_valides_tr = _all_actions_historique_precalc if _op_tr == "ACHAT" else _actions_possedees_precalc
                    # Même principe que le pré-remplissage depuis un document du courtier : on remet
                    # d'abord tous les champs du formulaire à zéro (dont date et heure, laissées vides
                    # pour que l'opérateur les renseigne), puis on y met les valeurs de la simulation.
                    for _k_tr in _IMPORT_TEXT_KEYS:
                        _ss_tr[_k_tr] = ""
                    for _k_tr in _IMPORT_OTHER_KEYS:
                        _ss_tr[_k_tr] = None
                    _ss_tr["k_op_type"] = _op_tr
                    if pos_existante is not None and nom_wi in _noms_valides_tr:
                        _ss_tr[f"{_pre_tr}_nom"] = nom_wi  # « Nouvelle valeur » : nom et ticker restent à saisir
                    _ss_tr[f"{_pre_tr}_qty"] = float(qte_wi)
                    _ss_tr[f"{_pre_tr}_prix"] = float(prix_wi)
                    _ss_tr[f"{_pre_tr}_comm"] = float(commission_wi)
                    if _op_tr == "ACHAT" and ttf_wi > 0:
                        _ss_tr["k_achat_ttf"] = float(ttf_wi)
                    if _DIALOG_SUPPORTS_DISMISS:
                        _ss_tr["_op_dialog_open"] = True
                        st.rerun()
                    else:
                        st.success("✅ Infos transférées : fermez cette fenêtre puis ouvrez « ➕ Nouvelle opération » (déjà pré-remplie).")

    elif type_wi == "Achat/Vente":
        # --- Simulation d'un ALLER-RETOUR achat puis revente ---
        # Autonome, sans lien avec une position déjà en portefeuille : on part d'un prix
        # d'achat et d'un montant à investir, et on calcule le prix de revente nécessaire pour
        # atteindre un objectif de gain donné (en € ou en %). Réutilise les MÊMES taux de
        # commission/TTF que les autres types de simulation ci-dessus (taux_courtier_pct_wi,
        # taux_ttf_pct_wi), avec ses propres cases à cocher Éligibilité TTF / Exonération
        # commission puisque ces deux réglages dépendent du sens de l'opération simulée.

        col_av_price, col_av_amount = st.columns(2)
        with col_av_price:
            prix_achat_av = st.number_input(
                "Prix d'achat unitaire (€)",
                min_value=0.0, step=0.0001, value=None, format="%.4f",
                placeholder="Entrez un prix...",
                key="k_whatif_av_prix_achat"
            )
        with col_av_amount:
            montant_av = st.number_input(
                "Montant à investir (€)",
                min_value=0.0, step=1.0, value=None,
                placeholder="Entrez un montant...",
                key="k_whatif_av_montant"
            )

        eligible_ttf_av = st.checkbox(
            "☑️ Éligible TTF (à l'achat)",
            key="k_whatif_av_eligible_ttf",
            help="À cocher si la valeur simulée est soumise à la TTF française : le taux ci-dessus sera alors appliqué à l'achat."
        )
        exoneration_commission_av = st.checkbox(
            "🚫 Exonération des commissions courtier (achat)",
            key="k_whatif_av_exoneration_commission",
            help="À cocher si l'achat est exonéré de commission courtier : le taux ci-dessus ne sera alors pas appliqué à l'achat."
        )

        _taux_c_av = 0.0 if exoneration_commission_av else (taux_courtier_pct_wi / 100.0)
        _taux_t_av = (taux_ttf_pct_wi / 100.0) if eligible_ttf_av else 0.0

        # Quantité réellement achetable avec le montant choisi, SANS DÉPASSER ce montant, frais
        # de courtier/TTF inclus (et pas seulement le prix des titres, comme avant) : diviser
        # uniquement par le prix pouvait donner une quantité dont le coût total réel (titres +
        # frais, cf. capital_investi_av plus bas) dépassait le montant que l'utilisateur avait
        # indiqué vouloir investir — d'où l'écart observé (ex. 100,34 € payés pour 100 € visés).
        # Comme la commission et la TTF sont chacune proportionnelles au montant brut acheté, le
        # coût total est lui aussi proportionnel à la quantité (à l'arrondi centime près) : la
        # quantité maximale s'obtient donc directement en divisant le montant à investir par le
        # "prix TTC" unitaire (prix × (1 + taux commission + taux TTF)), puis on redescend d'une
        # action si besoin pour rattraper un éventuel dépassement d'un centime dû aux arrondis
        # (commission et TTF sont chacune arrondies séparément à 2 décimales plus bas, ce qui
        # peut différer très légèrement du calcul continu utilisé ici pour l'estimation initiale).
        quantite_av = 0
        if prix_achat_av and prix_achat_av > 0 and montant_av and montant_av > 0:
            _taux_total_frais_av = _taux_c_av + _taux_t_av
            quantite_av = int(montant_av // (prix_achat_av * (1 + _taux_total_frais_av)))
            while quantite_av > 0:
                _mb_test_av = round(quantite_av * prix_achat_av, 2)
                _comm_test_av = 0.0 if exoneration_commission_av else round(_mb_test_av * _taux_c_av, 2)
                _ttf_test_av = round(_mb_test_av * _taux_t_av, 2) if eligible_ttf_av else 0.0
                if round(_mb_test_av + _comm_test_av + _ttf_test_av, 2) <= montant_av + 1e-9:
                    break
                quantite_av -= 1

        st.markdown("<hr style='margin:14px 0;'>", unsafe_allow_html=True)

        if not prix_achat_av or not montant_av or quantite_av < 1:
            st.markdown(
                '<div style="padding: 20px; background:#f8fafc; border:1px dashed #cbd5e1; border-radius:12px; text-align:center; color:#64748b;">'
                '<div style="font-size:1.4rem;">💱</div>'
                '<div style="font-size:0.88rem; font-weight:600; margin-top:6px;">Renseignez un prix d\'achat et un montant à investir pour lancer la simulation</div></div>',
                unsafe_allow_html=True
            )
        else:
            montant_brut_achat_av = round(quantite_av * prix_achat_av, 2)
            commission_achat_av = 0.0 if exoneration_commission_av else round(montant_brut_achat_av * _taux_c_av, 2)
            ttf_achat_av = round(montant_brut_achat_av * _taux_t_av, 2) if eligible_ttf_av else 0.0
            frais_achat_av = round(commission_achat_av + ttf_achat_av, 2)
            capital_investi_av = round(montant_brut_achat_av + frais_achat_av, 2)
            prix_achat_net_av = capital_investi_av / quantite_av

            _detail_frais_achat_av = []
            if commission_achat_av > 0:
                _detail_frais_achat_av.append(f"commission {fmt_eur(commission_achat_av)}")
            elif exoneration_commission_av:
                _detail_frais_achat_av.append("commission exonérée")
            if ttf_achat_av > 0:
                _detail_frais_achat_av.append(f"TTF {fmt_eur(ttf_achat_av)}")
            _detail_frais_achat_str_av = " + ".join(_detail_frais_achat_av) if _detail_frais_achat_av else "aucun frais"

            # --- Achat : prix par action brut / net de frais, puis quantité achetable et montant total payé ---
            _sim_headline_duo([
                ("Prix d'achat / action brut de frais", fmt_price_dynamic(prix_achat_av, include_comm=False), "", False),
                ("Prix d'achat / action net de frais", fmt_price_dynamic(prix_achat_net_av, include_comm=False),
                 _detail_frais_achat_str_av, True, "#1d4ed8"),
            ])
            _sim_headline_duo([
                ("Quantité achetable", f"{quantite_av:g}", "action(s)", False),
                ("Montant total payé", fmt_eur(capital_investi_av), "frais inclus", False, "#0f172a"),
            ])

            # --- Deux boutons : objectif de gain à la revente / gain en vendant à un prix donné ---
            if "k_whatif_av_mode" not in st.session_state:
                st.session_state["k_whatif_av_mode"] = None

            def _av_set_mode(m):
                st.session_state["k_whatif_av_mode"] = m

            _mode_av = st.session_state["k_whatif_av_mode"]
            st.markdown("<div style='height:6px;'></div>", unsafe_allow_html=True)
            with st.container(key="compact_cols_av_mode"):
                _cb1, _cb2 = st.columns(2)
                _cb1.button("🎯 Objectif de gain à la revente", key="k_whatif_av_btn_obj", use_container_width=True,
                            type=("primary" if _mode_av == "objectif" else "secondary"),
                            on_click=_av_set_mode, args=("objectif",))
                _cb2.button("💹 Gain si je vends à un prix", key="k_whatif_av_btn_prix", use_container_width=True,
                            type=("primary" if _mode_av == "prix" else "secondary"),
                            on_click=_av_set_mode, args=("prix",))

            if _mode_av is None:
                st.caption("Choisissez un des deux boutons ci-dessus pour simuler la revente.")
            else:
                # Exonération de commission COURTIER À LA VENTE, indépendante de celle de l'achat (une offre de
                # courtage gratuit peut ne s'appliquer qu'à l'achat, ou inversement).
                exoneration_commission_vente_av = st.checkbox(
                    "🚫 Exonération des commissions courtier (vente)",
                    key="k_whatif_av_exoneration_commission_vente",
                    help="À cocher si la revente est exonérée de commission courtier : le taux ci-dessus ne sera alors pas appliqué à la vente."
                )
                _taux_c_vente_av = 0.0 if exoneration_commission_vente_av else (taux_courtier_pct_wi / 100.0)

            if _mode_av == "objectif":
                # Les deux champs (€ et %) restent synchronisés via deux callbacks on_change : modifier l'un recalcule
                # immédiatement l'autre à partir du capital investi net de frais. La mise à jour de session_state se
                # fait dans le callback, donc AVANT que le widget ne soit ré-instancié au rerun suivant.
                # "k_whatif_av_last_field" mémorise LEQUEL des deux champs a été saisi en dernier : si le prix d'achat
                # ou le montant changent ensuite (donc le capital investi), on recalcule automatiquement l'AUTRE champ.
                def _av_on_gain_eur_change():
                    st.session_state["k_whatif_av_last_field"] = "eur"
                    if capital_investi_av > 0:
                        st.session_state["k_whatif_av_gain_pct"] = round(
                            st.session_state["k_whatif_av_gain_eur"] / capital_investi_av * 100, 2
                        )
                    st.session_state["k_whatif_av_capital_prev"] = capital_investi_av

                def _av_on_gain_pct_change():
                    st.session_state["k_whatif_av_last_field"] = "pct"
                    if capital_investi_av > 0:
                        st.session_state["k_whatif_av_gain_eur"] = round(
                            st.session_state["k_whatif_av_gain_pct"] / 100 * capital_investi_av, 2
                        )
                    st.session_state["k_whatif_av_capital_prev"] = capital_investi_av

                if "k_whatif_av_gain_eur" not in st.session_state:
                    st.session_state["k_whatif_av_gain_eur"] = 0.0
                if "k_whatif_av_gain_pct" not in st.session_state:
                    st.session_state["k_whatif_av_gain_pct"] = 0.0
                if "k_whatif_av_last_field" not in st.session_state:
                    st.session_state["k_whatif_av_last_field"] = "pct"
                if "k_whatif_av_capital_prev" not in st.session_state:
                    st.session_state["k_whatif_av_capital_prev"] = capital_investi_av

                if abs(capital_investi_av - st.session_state["k_whatif_av_capital_prev"]) > 1e-9:
                    if st.session_state["k_whatif_av_last_field"] == "eur":
                        if capital_investi_av > 0:
                            st.session_state["k_whatif_av_gain_pct"] = round(
                                st.session_state["k_whatif_av_gain_eur"] / capital_investi_av * 100, 2
                            )
                    else:
                        if capital_investi_av > 0:
                            st.session_state["k_whatif_av_gain_eur"] = round(
                                st.session_state["k_whatif_av_gain_pct"] / 100 * capital_investi_av, 2
                            )
                    st.session_state["k_whatif_av_capital_prev"] = capital_investi_av

                with st.container(key="compact_cols_av_gain"):
                    col_gain_eur_av, col_gain_pct_av = st.columns(2)
                    with col_gain_eur_av:
                        st.number_input(
                            "Gain souhaité (€)",
                            step=0.01, format="%.2f",
                            key="k_whatif_av_gain_eur",
                            on_change=_av_on_gain_eur_change,
                            help="Le gain net souhaité (après commission de revente), en euros. Modifiez ce champ ou celui de droite : les deux restent synchronisés."
                        )
                    with col_gain_pct_av:
                        st.number_input(
                            "Gain souhaité (%)",
                            step=0.01, format="%.2f",
                            key="k_whatif_av_gain_pct",
                            on_change=_av_on_gain_pct_change,
                            help="Le même gain souhaité, exprimé en pourcentage du montant total payé à l'achat (frais inclus)."
                        )

                gain_eur_cible_av = float(st.session_state.get("k_whatif_av_gain_eur", 0.0))

                if abs(1.0 - _taux_c_vente_av) < 1e-9:
                    st.warning("⚠️ Taux de commission de 100% invalide pour le calcul du prix de vente.")
                else:
                    # \"Brut de frais de vente\" = prix nécessaire pour le gain visé SANS tenir compte de la commission
                    # de vente ; \"net de frais de vente\" = prix RÉEL à saisir dans l'ordre pour qu'une fois la
                    # commission de vente déduite, le gain visé soit atteint (donc plus élevé que le brut).
                    montant_vente_net_cible_av = gain_eur_cible_av + capital_investi_av
                    prix_vente_brut_av = montant_vente_net_cible_av / quantite_av
                    montant_vente_net_reel_av = montant_vente_net_cible_av / (1.0 - _taux_c_vente_av)
                    prix_vente_net_av = montant_vente_net_reel_av / quantite_av
                    _sim_headline_duo([
                        ("Prix de vente / action brut de frais de vente", fmt_price_dynamic(prix_vente_brut_av, include_comm=False), "", False),
                        ("Prix de vente / action net de frais de vente", fmt_price_dynamic(prix_vente_net_av, include_comm=False), "à saisir dans l'ordre", True, "#7c3aed"),
                    ])
                    _sim_headline("Montant total de vente", fmt_eur(montant_vente_net_reel_av), "", "#7c3aed")

            elif _mode_av == "prix":
                with st.container(key="compact_cols_av_prixvente"):
                    prix_vente_saisi_av = st.number_input(
                        "Prix de vente par action (€)",
                        min_value=0.0, step=0.0001, value=None, format="%.4f",
                        placeholder="Entrez un prix de vente...",
                        key="k_whatif_av_prix_vente",
                    )
                if prix_vente_saisi_av and prix_vente_saisi_av > 0:
                    montant_vente_brut_av = round(quantite_av * prix_vente_saisi_av, 2)
                    commission_vente_av = round(montant_vente_brut_av * _taux_c_vente_av, 2)
                    montant_vente_recu_av = round(montant_vente_brut_av - commission_vente_av, 2)
                    gain_brut_av = round(montant_vente_brut_av - montant_brut_achat_av, 2)      # hors tous frais
                    gain_net_av = round(montant_vente_recu_av - capital_investi_av, 2)           # après frais d'achat et de vente
                    gain_pct_av = (gain_net_av / capital_investi_av * 100) if capital_investi_av > 0 else 0.0
                    _col_pct = "#16a34a" if gain_net_av > 0.005 else ("#dc2626" if gain_net_av < -0.005 else "#64748b")
                    _col_brut = "#16a34a" if gain_brut_av > 0.005 else ("#dc2626" if gain_brut_av < -0.005 else "#64748b")
                    _sg = lambda v: ("+" if v > 0.005 else "") + fmt_eur(v)
                    gain_brut_pct_av = (gain_brut_av / montant_brut_achat_av * 100) if montant_brut_achat_av > 0 else 0.0
                    _pct_txt = lambda v: ("+" if v > 0.005 else "") + f"{v:,.2f} %".replace(",", " ").replace(".", ",")
                    _col_brut_pct = "#16a34a" if gain_brut_pct_av > 0.005 else ("#dc2626" if gain_brut_pct_av < -0.005 else "#64748b")

                    def _gain_duo(items):
                        _bgs = {"#16a34a": ("#f0fdf4", "#86efac"), "#dc2626": ("#fef2f2", "#fca5a5")}
                        parts = []
                        for lab, val, col in items:
                            bg, bd = _bgs.get(col, ("#f8fafc", "#e2e8f0"))
                            parts.append(
                                f'<div class="pea-duo-item" style="background:{bg}; border:1px solid {bd}; border-top:3px solid {col};">'
                                f'<div class="k">{lab}</div><div class="v" style="color:{col};">{val}</div></div>'
                            )
                        st.markdown(f'<div class="pea-duo">{"".join(parts)}</div>', unsafe_allow_html=True)

                    _gain_duo([
                        ("Gain brut en %", _pct_txt(gain_brut_pct_av), _col_brut_pct),
                        ("Gain brut en €", _sg(gain_brut_av), _col_brut),
                    ])
                    _gain_duo([
                        ("Gain net en %", _pct_txt(gain_pct_av), _col_pct),
                        ("Gain net en €", _sg(gain_net_av), _col_pct),
                    ])
                    st.markdown(
                        '<div style="margin-top:8px; padding:10px 14px; background:linear-gradient(135deg,#f5f3ff,#ede9fe); '
                        'border:1px solid #c4b5fd; border-left:4px solid #7c3aed; border-radius:10px; '
                        'display:flex; justify-content:space-between; align-items:center; gap:10px; flex-wrap:wrap;">'
                        '<span style="font-size:0.7rem; color:#6d28d9; text-transform:uppercase; font-weight:800; letter-spacing:0.05em;">💰 Montant total vendu</span>'
                        f'<span style="font-size:1.25rem; font-weight:800; color:#5b21b6;">{fmt_eur(montant_vente_brut_av)}</span></div>',
                        unsafe_allow_html=True,
                    )

    else:
        # --- Simulation d'un SPLIT / regroupement ---
        if pos_existante is None:
            st.info("Choisissez une valeur détenue pour simuler un split.")
        else:
            facteur_wi = st.number_input(
                "Facteur de split (ex : 2 pour un split 2-pour-1, 0,5 pour un regroupement 1-pour-2)",
                min_value=0.0001, step=0.1, value=2.0, key="k_whatif_split_facteur"
            )
            rompu_wi = st.number_input(
                "Rompu versé en cash (€) — optionnel", min_value=0.0, step=0.01, value=0.0, key="k_whatif_split_rompu"
            )

            qte_avant = float(pos_existante["Quantité"])
            pru_avant = float(pos_existante["PRU Net (€)"])
            invested_avant = float(pos_existante["Capital Investi (€)"])
            prix_actuel_wi = float(pos_existante["Prix Actuel (€)"])
            _history_wi_split = get_portfolio_history(df_transactions)
            cash_avant = 0.0
            if _history_wi_split is not None and not _history_wi_split.empty:
                cash_avant = _history_wi_split["Poche Espèces (€)"].iloc[-1]

            qte_apres = qte_avant * facteur_wi
            # Le capital investi total ne change pas avec un split (hors rompu réglé en cash) :
            # seul le PRU par titre est mécaniquement divisé par le facteur.
            invested_apres = max(invested_avant - rompu_wi, 0.0)
            pru_apres = invested_apres / qte_apres if qte_apres > 0.0001 else 0.0
            prix_apres_wi = prix_actuel_wi / facteur_wi if facteur_wi > 0 else prix_actuel_wi
            cash_apres = cash_avant + rompu_wi

            st.markdown("<hr style='margin:14px 0;'>", unsafe_allow_html=True)
            d_cash, c_cash = _delta_eur(cash_apres - cash_avant)
            d_qte = qte_apres - qte_avant
            d_qte_color = "#16a34a" if d_qte > 0 else ("#dc2626" if d_qte < 0 else "#64748b")
            d_qte_str = f"{_arrow_sym(d_qte, 1e-9)} {'+' if d_qte > 0 else ''}{d_qte:g} titre(s)"
            d_pru, c_pru = _delta_prix(pru_apres - pru_avant)

            _render_before_after([
                ("💰 Poche espèces", fmt_eur(cash_avant), fmt_eur(cash_apres), d_cash, c_cash),
                ("📦 Quantité détenue", f"{qte_avant:g}", f"{qte_apres:g}", d_qte_str, d_qte_color),
                ("🎯 PRU net", fmt_price_dynamic(pru_avant, include_comm=False), fmt_price_dynamic(pru_apres, include_comm=False), d_pru, c_pru),
            ])
            st.caption(f"Nouveau prix théorique du titre après split : {fmt_eur(prix_apres_wi)} (contre {fmt_eur(prix_actuel_wi)} avant).")

# ==========================================
# 3. HISTORIQUE GLOBAL & TWR
# ==========================================
@st.cache_data(ttl=None, max_entries=600, show_spinner=False)
def _ticker_position_series_cached(ticker, df_ticker, start_date_str, end_date_str):
    """Partie « positions » du calcul quotidien d'UN ticker : titres détenus, capital investi,
    gain réalisé et dividendes cumulés, jour par jour. Elle ne dépend QUE des opérations du
    ticker et des deux dates (aucun cours), donc son résultat est mémorisé sans expiration : la clé
    change d'elle-même quand une opération est ajoutée/modifiée ou quand la date du jour change.
    Avant, cette boucle était refaite pour tous les tickers toutes les 5 minutes en même temps
    que la valorisation aux cours, alors que seule celle-ci évolue avec les cours."""
    all_dates = pd.date_range(start=start_date_str, end=end_date_str)

    def custom_sort_key_hist(row):
        t = row["Type"]
        if t in ("SPLIT", "ROMPU_PAYE"):
            h = time(0, 0, 0)
        else:
            h = row["Date_Heure"].time()
        return (row["Date_Heure"].date(), h)

    _records_ticker = df_ticker.to_dict('records')

    # Un SPLIT peut avoir une date de versement des rompus (Date_Rompus) différente de la
    # date du split elle-même (Date_Heure) : le nombre de titres change à la date du split,
    # mais le cash correspondant aux rompus peut n'être crédité que quelques jours plus
    # tard. On sépare donc les deux effets en un événement synthétique "ROMPU_PAYE", placé
    # à sa propre date, pour que "Dividendes Cumulés (€)" ne compte ce montant qu'à partir
    # du jour où il est réellement versé.
    _records_final = []
    for rec in _records_ticker:
        if rec["Type"] == "SPLIT":
            _rompu_amt = rec.get("Rompu", 0.0)
            if pd.notnull(_rompu_amt) and _rompu_amt > 0:
                _date_rompu_rec = rec.get("Date_Rompus")
                if pd.isnull(_date_rompu_rec):
                    _date_rompu_rec = rec["Date_Heure"]
                if _date_rompu_rec != rec["Date_Heure"]:
                    rec = dict(rec)
                    rec["Rompu"] = 0.0
                    _records_final.append(rec)
                    _records_final.append({
                        "Date_Heure": _date_rompu_rec, "Type": "ROMPU_PAYE", "Rompu": _rompu_amt,
                        "Quantité": 0.0, "Prix Unitaire (€)": 0.0, "Frais Totaux (€)": 0.0,
                        "Commission (€)": 0.0, "Retenue_Source_Etrangere": 0.0, "Remboursement_Capital": 0.0,
                    })
                    continue
        _records_final.append(rec)

    sorted_rows = sorted(_records_final, key=custom_sort_key_hist)

    # Tableaux numpy + position de chaque jour dans all_dates calculée UNE SEULE FOIS pour toutes
    # les opérations (get_indexer, vectorisé) : avant, chaque opération faisait 4 fois
    # `serie.loc[d:] = valeur` sur un pd.Series de 1300+ jours, or chaque affectation .loc passe
    # par toute la mécanique d'indexation de pandas (recherche de la date, construction de la
    # tranche, vérifications de type...) : c'était >90 % du temps de ce calcul. Un
    # `tableau[pos:] = valeur` numpy fait exactement la même chose (remplir du jour de
    # l'opération jusqu'à la fin) en quelques microsecondes. Les valeurs obtenues sont
    # strictement identiques ; get_indexer renvoie -1 pour une date hors de all_dates, ce qui
    # reproduit le `if d in index` d'origine (opération ignorée dans la série).
    _n_dates_h = len(all_dates)
    _arr_shares = np.zeros(_n_dates_h)
    _arr_invested = np.zeros(_n_dates_h)
    _arr_realized = np.zeros(_n_dates_h)
    _arr_divs = np.zeros(_n_dates_h)
    _pos_rows = all_dates.get_indexer(pd.DatetimeIndex([r["Date_Heure"] for r in sorted_rows]).normalize())

    current_shares, current_invested = 0.0, 0.0
    current_realized, current_divs = 0.0, 0.0

    for _k_row, row in enumerate(sorted_rows):
        t, qty, p, f = row["Type"], row["Quantité"], row["Prix Unitaire (€)"], row["Frais Totaux (€)"]
        comm = row.get("Commission (€)", 0.0)
        rompu = row.get("Rompu", 0.0)
        ret_etr = row.get("Retenue_Source_Etrangere", 0.0)
        remb_capital_hist = row.get("Remboursement_Capital", 0.0)
        arrondi_courtier_hist = row.get("Arrondi_Courtier", 0.0)

        if t == "ACHAT":
            current_shares += qty
            current_invested += (qty * p) + f
        elif t == "VENTE":
            if current_shares > 0:
                pru = current_invested / current_shares
                sale_rev = (qty * p) - f
                current_realized += (sale_rev - (qty * pru))
                current_shares -= qty
                current_invested = current_shares * pru
        elif t == "SPLIT":
            if current_shares > 0:
                brute_shares = current_shares * qty
                integer_shares = int(brute_shares)
                current_shares = integer_shares
            # Le rompu de cette ligne (s'il a la même date que le split) a été laissé tel
            # quel ci-dessus ; s'il avait une date différente, il a déjà été extrait plus
            # haut en un événement "ROMPU_PAYE" séparé.
            if pd.notnull(rompu) and rompu > 0:
                current_divs += rompu
        elif t == "ROMPU_PAYE":
            current_divs += rompu
        elif t == "DIVIDENDE":
            arrondi_courtier_hist_val = arrondi_courtier_hist if pd.notnull(arrondi_courtier_hist) else 0.0
            net_div = p - ret_etr - comm + arrondi_courtier_hist_val
            current_divs += net_div
            # Remboursement de capital inclus dans le dividende (ex. Schneider Electric) :
            # ce n'est pas un gain, cela réduit mécaniquement le capital investi (donc le PRU)
            # de la ligne, exactement comme dans compute_portfolio_metrics_cached.
            if pd.notnull(remb_capital_hist) and remb_capital_hist > 0:
                current_invested = max(0.0, current_invested - remb_capital_hist)

        _pos_d = _pos_rows[_k_row]
        if _pos_d >= 0:
            _arr_shares[_pos_d:] = current_shares
            _arr_invested[_pos_d:] = current_invested
            _arr_realized[_pos_d:] = current_realized
            _arr_divs[_pos_d:] = current_divs

    daily_shares = pd.Series(_arr_shares, index=all_dates)
    daily_invested = pd.Series(_arr_invested, index=all_dates)
    daily_realized = pd.Series(_arr_realized, index=all_dates)
    daily_divs = pd.Series(_arr_divs, index=all_dates)
    return daily_shares, daily_invested, daily_realized, daily_divs, current_shares, current_invested


@st.cache_data(ttl=300, show_spinner=False)
def _compute_ticker_daily_history_cached(ticker, df_ticker, start_date_str, end_date_str):
    """Calcule la série quotidienne (valeur, capital investi, gain réalisé cumulé, dividendes
    cumulés) d'UN SEUL ticker, sur toute la période 'all_dates' — logique RIGOUREUSEMENT
    IDENTIQUE à avant (même boucle jour par jour sur les opérations triées, même alignement sur
    les cours historiques), simplement isolée dans sa propre fonction mise en cache plutôt que
    noyée dans le calcul de tout le portefeuille.

    L'intérêt : la clé de cache de st.cache_data se base sur ses arguments, donc sur df_ticker
    (les seules opérations de CE ticker). Ajouter ou modifier une opération sur une valeur
    n'invalide donc plus QUE le cache de cette valeur-là : les autres tickers du portefeuille,
    dont les opérations n'ont pas changé, gardent leur série déjà calculée au lieu d'être
    recalculée elle aussi. Avant ce découpage, get_portfolio_history_cached était mise en cache
    globalement sur tout l'historique des transactions : la moindre opération, même sur un seul
    titre, changeait cette clé de cache et forçait à refaire toute la boucle jour par jour depuis
    l'ouverture du PEA pour TOUS les titres — c'était la cause de la latence sur la validation
    d'une opération.

    Reçoit start_date_str / end_date_str (des chaînes) plutôt que directement all_dates (un
    DatetimeIndex) : st.cache_data doit pouvoir "hacher" chaque argument pour construire sa clé
    de cache, et il ne sait pas le faire pour un DatetimeIndex (erreur UnhashableParamError) —
    deux chaînes de caractères, en revanche, se hachent sans problème. all_dates est donc
    reconstruit ici, à l'identique de get_portfolio_history_cached, à partir de ces deux bornes."""
    all_dates = pd.date_range(start=start_date_str, end=end_date_str)
    daily_shares, daily_invested, daily_realized, daily_divs, current_shares, current_invested = _ticker_position_series_cached(
        ticker, df_ticker, start_date_str, end_date_str)

    try:
        # get_ticker_history est elle-même mise en cache séparément (voir sa définition) et
        # déjà préchargée en parallèle pour tous les tickers juste avant l'appel à cette
        # fonction (voir get_portfolio_history_cached) : cet appel retombe donc sur un cache
        # déjà chaud dans l'immense majorité des cas, sans nouvelle requête réseau.
        hist_df = get_ticker_history(ticker, start_date_str)
        if hist_df is not None and not hist_df.empty and "Close" in hist_df.columns:
            hist = hist_df["Close"]
        else:
            hist = pd.Series(dtype=float)

        if hasattr(hist.index, "tz_localize") and hist.index.tz is not None:
            hist.index = hist.index.tz_localize(None)

        aligned_hist = hist.reindex(all_dates).ffill().bfill()

        # Bougie de la veille absente de l'historique Yahoo (cache, retard de publication) : sans correctif, la
        # veille recopie une clôture plus ancienne, sa variation est nulle (journée masquée dans l'historique) et
        # le mouvement des deux jours se retrouve sur « aujourd'hui ». Une fois la séance ouverte (9 h à Paris),
        # on comble avec la clôture précédente fournie par Yahoo.
        try:
            _bars = hist.dropna()
            _today_n = all_dates[-1]
            if len(_bars) and _marche_ouvert_aujourdhui() and _today_n == _today_paris():
                _veille = _today_n - pd.Timedelta(days=1)
                while _veille.weekday() >= 5:
                    _veille -= pd.Timedelta(days=1)
                if _veille not in set(_bars.index.normalize()) and _veille >= all_dates[0]:
                    _pc = get_previous_close(ticker)
                    if _pc:
                        aligned_hist.loc[_veille:_today_n - pd.Timedelta(days=1)] = _pc
        except Exception:
            pass

        live_p = get_live_price(ticker)
        if live_p is not None and not np.isnan(live_p):
            aligned_hist.iloc[-1] = live_p

        if aligned_hist.isna().all() and current_shares > 0 and current_invested > 0:
            fallback_p = current_invested / current_shares
            aligned_hist = aligned_hist.fillna(fallback_p)

        daily_value = daily_shares * aligned_hist
    except Exception:
        fallback_p = (current_invested / current_shares) if current_shares > 0 else 0
        daily_value = daily_shares * (get_live_price(ticker) or fallback_p)

    return pd.DataFrame({
        "valeur": daily_value,
        "investi": daily_invested,
        "realise": daily_realized,
        "dividendes": daily_divs,
    }, index=all_dates)


@st.cache_data(ttl=300, show_spinner=False)
def get_portfolio_history_cached(df_in):
    df = df_in.copy()
    if df.empty:
        return None
    
    start_date = df["Date_Heure"].min().normalize()
    end_date = _today_paris()
    all_dates = pd.date_range(start=start_date, end=end_date)
    end_date_str = end_date.strftime("%Y-%m-%d")
    
    portfolio_values = pd.DataFrame(index=all_dates)
    invested_capital_values = pd.DataFrame(index=all_dates)
    realized_pnl_values = pd.DataFrame(index=all_dates) 
    dividends_values = pd.DataFrame(index=all_dates) 

    df_actions = df[~df["Type"].isin(["APPORT", "RETRAIT"])].copy()
    tickers = df_actions["Ticker"].unique() if not df_actions.empty else []

    # Préchargement parallèle des historiques de cours (mêmes données, même appel yfinance,
    # simplement lancés en même temps pour tous les tickers au lieu d'un par un) : sert
    # uniquement à "chauffer" le cache de get_ticker_history avant que
    # _compute_ticker_daily_history_cached ne l'appelle ticker par ticker plus bas — la valeur
    # de retour n'est pas conservée ici, seul le cache l'est.
    start_date_str = start_date.strftime("%Y-%m-%d")

    def _fetch_hist_raw(t):
        return t, get_ticker_history(t, start_date_str)

    _tickers_valides = [t for t in tickers if t and t not in _FAILED_TICKERS]
    if _tickers_valides:
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(_tickers_valides))) as executor:
            list(executor.map(_fetch_hist_raw, _tickers_valides))

    # Chaque ticker est calculé par _compute_ticker_daily_history_cached, mise en cache
    # INDÉPENDAMMENT pour chacun (voir sa définition ci-dessus) : c'est ce qui rend ce calcul
    # incrémental d'un ticker à l'autre.
    for ticker in tickers:
        df_ticker = df_actions[df_actions["Ticker"] == ticker]
        ticker_series = _compute_ticker_daily_history_cached(ticker, df_ticker, start_date_str, end_date_str)
        portfolio_values[ticker] = ticker_series["valeur"]
        invested_capital_values[ticker] = ticker_series["investi"]
        realized_pnl_values[ticker] = ticker_series["realise"]
        dividends_values[ticker] = ticker_series["dividendes"]

    result_df = pd.DataFrame(index=all_dates)
    result_df["Valeur Actions (€)"] = portfolio_values.sum(axis=1) if not portfolio_values.empty else 0
    result_df["Capital Investi Total (€)"] = invested_capital_values.sum(axis=1) if not invested_capital_values.empty else 0
    result_df["Gain Réalisé Cumulé (€)"] = realized_pnl_values.sum(axis=1) if not realized_pnl_values.empty else 0
    result_df["Dividendes Cumulés (€)"] = dividends_values.sum(axis=1) if not dividends_values.empty else 0

    # Pour le cash, un SPLIT n'a d'impact que via ses rompus (le split lui-même ne fait que
    # transformer des titres en d'autres titres, sans mouvement de cash) : on peut donc, pour
    # cette boucle uniquement, dater ces lignes à leur date de versement réelle des rompus
    # (Date_Rompus) plutôt qu'à la date du split, sans affecter aucun autre type d'opération.
    df_mouv = df.copy()
    _mask_split_cash = df_mouv["Type"] == "SPLIT"
    if "Date_Rompus" in df_mouv.columns:
        df_mouv.loc[_mask_split_cash, "Date_Heure"] = df_mouv.loc[_mask_split_cash, "Date_Rompus"].fillna(df_mouv.loc[_mask_split_cash, "Date_Heure"])
    df_mouv = df_mouv.sort_values("Date_Heure")
    # Même principe que dans _compute_ticker_daily_history_cached : tableau numpy + positions
    # des jours calculées en une passe (au lieu d'un `.loc[d:] = ...` pandas par opération), et
    # itération sur to_dict("records") plutôt que .iterrows() (qui reconstruit une Series par
    # ligne). Résultat strictement identique.
    _arr_cash = np.zeros(len(all_dates))
    _pos_cash = all_dates.get_indexer(pd.DatetimeIndex(df_mouv["Date_Heure"]).normalize())

    current_cash_val = 0.0
    for _k_cash, row in enumerate(df_mouv.to_dict("records")):
        t = row["Type"]
        qty = row["Quantité"]
        p = row["Prix Unitaire (€)"]
        f = row["Frais Totaux (€)"]
        comm = row.get("Commission (€)", 0.0)
        ret_etr = row.get("Retenue_Source_Etrangere", 0.0)
        rompu = row.get("Rompu", 0.0)
        
        if t == "APPORT":
            current_cash_val = _round_cash(current_cash_val, qty)
        elif t == "RETRAIT":
            current_cash_val = _round_cash(current_cash_val, -qty)
        elif t == "ACHAT":
            # Même logique que compute_cash_actuel_cached (voir _montant_ordre et _round_cash) :
            # arrondi au centime, comme le fait réellement le courtier sur l'avis d'opéré, AVANT
            # de retrancher le montant du cash cumulé — au lieu d'accumuler des résidus de
            # sous-centime au fil des transactions, qui créaient un écart de quelques centimes
            # avec le solde espèces réellement affiché par le courtier.
            current_cash_val = _round_cash(current_cash_val, -_montant_ordre(qty, p, f))
        elif t == "VENTE":
            current_cash_val = _round_cash(current_cash_val, _montant_ordre(qty, p, -f))
        elif t == "DIVIDENDE":
            remb_capital_cash = row.get("Remboursement_Capital", 0.0)
            remb_capital_cash = remb_capital_cash if pd.notnull(remb_capital_cash) else 0.0
            arrondi_courtier_cash = row.get("Arrondi_Courtier", 0.0)
            arrondi_courtier_cash = arrondi_courtier_cash if pd.notnull(arrondi_courtier_cash) else 0.0
            current_cash_val = _round_cash(current_cash_val, p, -ret_etr, -comm, remb_capital_cash, arrondi_courtier_cash)
        elif t == "SPLIT":
            if pd.notnull(rompu) and rompu > 0:
                current_cash_val = _round_cash(current_cash_val, rompu)

        if _pos_cash[_k_cash] >= 0:
            _arr_cash[_pos_cash[_k_cash]:] = current_cash_val

    result_df["Poche Espèces (€)"] = pd.Series(_arr_cash, index=all_dates)
    
    _df_apports = df[df["Type"].isin(["APPORT", "RETRAIT"])].sort_values("Date_Heure")
    _arr_apports = np.zeros(len(all_dates))
    _pos_apports = all_dates.get_indexer(pd.DatetimeIndex(_df_apports["Date_Heure"]).normalize())
    curr_apports = 0.0
    for _k_app, row in enumerate(_df_apports.to_dict("records")):
        if row["Type"] == "APPORT":
            curr_apports += row["Quantité"]
        else:
            curr_apports -= row["Quantité"]
        if _pos_apports[_k_app] >= 0:
            _arr_apports[_pos_apports[_k_app]:] = curr_apports
            
    result_df["Apports Cumulés (€)"] = pd.Series(_arr_apports, index=all_dates)
    result_df["Valeur du Portefeuille (€)"] = result_df["Valeur Actions (€)"] + result_df["Poche Espèces (€)"]

    return result_df

def get_portfolio_history(df):
    return get_portfolio_history_cached(df)


# ==========================================
# 4. INTERFACE PRINCIPALE
# ==========================================
_titre_nom = (app_config.get("user_name") or "").strip()
st.title("📊 Tableau de Bord PEA" + (f" - {_titre_nom}" if _titre_nom else ""))

if not df_transactions.empty:
    pea_opening_dt = df_transactions["Date_Heure"].min()
    pea_opening_date = pea_opening_dt.strftime("%d-%m-%Y")
    
    today_date = _today_paris()
    diff = relativedelta(today_date, pea_opening_dt.normalize())
    anciennete_str = f"{diff.years} an(s) {diff.months} mois {diff.days} jour(s)"

    st.markdown(
        f"🗓️ **Date d'ouverture du PEA :** {pea_opening_date}  \n"
        f"<span style='color:#64748b;'>(Ancienneté : **{anciennete_str}**)</span>",
        unsafe_allow_html=True,
    )
else:
    st.markdown("🗓️ **Date d'ouverture du PEA :** Aucune transaction")
st.markdown(f"🏦 **Courtier :** **{app_config.get('broker', 'Non renseigné')}**")

# Note : le réglage "Commission courtier (%)" qui vivait ici en permanence sur le dashboard a
# été retiré (redondant avec le même réglage, disponible et modifiable directement en haut de
# la fenêtre "🧪 Simulation nouvelle opération", qui met à jour la même configuration partagée).

# Réglages d'affichage (colonne gauche) + bouton d'ajout (colonne droite, aligné sur la moitié
# horizontale de la fenêtre) placés dans la même rangée, juste sous le courtier.
# Ce bloc reste ICI, avant le calcul lourd de l'historique (get_portfolio_history, qui
# interroge yfinance) : Streamlit ré-exécute tout le script à chaque clic, donc plus la
# ligne du bouton apparaît tôt dans le script, plus vite la fenêtre modale s'ouvre. Placé
# après les calculs coûteux comme avant, l'ouverture devait attendre leur fin (~5s au
# premier appel, tant que le cache st.cache_data n'est pas encore chaud).
col_toggles = st.container()
with col_toggles:
    # Indicateurs de synthèse utilisés par les deux exports (XML et PDF) ci-dessous. "Valeur",
    # "PlusValueLatente", "Dividende" et "Frais" viennent de compute_portfolio_metrics, déjà
    # calculé plus haut (cours en direct, mais un seul prix par titre, pas tout un historique).
    # Seul "Cash" a besoin d'un calcul dédié (compute_cash_actuel) : volontairement LÉGER (pas
    # d'appel yfinance ni de reconstruction jour par jour) pour ne pas retarder l'affichage de
    # ces boutons, placés ici avant le calcul lourd de l'historique (voir commentaire ci-dessus).
    _export_apports_totaux = (
        df_transactions[df_transactions["Type"] == "APPORT"]["Quantité"].sum()
        - df_transactions[df_transactions["Type"] == "RETRAIT"]["Quantité"].sum()
    ) if not df_transactions.empty else 0.0
    _export_cash = compute_cash_actuel(df_transactions)
    _export_valeur = tot_value_actions
    _export_plus_value_latente = tot_value_actions - tot_invested
    _export_performance = (
        ((_export_valeur + _export_cash - _export_apports_totaux) / _export_apports_totaux) * 100
        if _export_apports_totaux > 0 else 0.0
    )

    # Un seul bouton « Exports / Imports » : les 3 exports (XML, PDF, CSV) et l'import CSV.
    import functools as _functools
    _TRANSAC_COLUMNS = [
        "Date_Heure", "Type", "Nom", "Ticker",
        "Quantité", "Prix Unitaire (€)", "Commission (€)",
        "TTF (€)", "Frais Totaux (€)", "Rompu", "Retenue_Source_Etrangere",
        "Remboursement_Capital", "Arrondi_Courtier", "Date_Rompus",
    ]
    with st.container(key="export_data_btn_wrap"):
        with st.popover("📦 Exports / Imports", use_container_width=True):
            st.markdown("**📤 Exports**")
            _export_tx_fp = None if _DEFERRED_DOWNLOAD else _export_signature(df_transactions)
            _export_xml_bytes, _export_xml_stamp = _export_payload(
                "xml",
                (
                    "xml", _export_tx_fp, _export_valeur, _export_cash, _export_apports_totaux,
                    _export_performance, _export_plus_value_latente, tot_dividends, tot_fees,
                ),
                _functools.partial(
                    generate_transactions_xml,
                    df_transactions,
                    valeur=_export_valeur, cash=_export_cash, total_apport=_export_apports_totaux,
                    performance=_export_performance, plus_value_latente=_export_plus_value_latente,
                    dividende_total=tot_dividends, frais_total=tot_fees,
                ),
            )
            st.download_button(
                label="📤 Exporter les données (XML)",
                data=_export_xml_bytes,
                file_name=f"ExportXML_{_export_xml_stamp}.xml",
                mime="application/xml",
                key="export_data_xml_btn",
                use_container_width=True,
            )
            _export_pdf_broker = app_config.get("broker", "")
            _export_pdf_ouverture = (df_transactions["Date_Heure"].min().strftime("%d/%m/%Y") if not df_transactions.empty else "")
            _export_pdf_bytes, _export_pdf_stamp = _export_payload(
                "pdf",
                (
                    "pdf", _export_tx_fp, df_port, _export_valeur, _export_cash, _export_apports_totaux,
                    _export_performance, _export_plus_value_latente, tot_dividends, tot_fees,
                    _export_pdf_broker, _export_pdf_ouverture,
                ),
                _functools.partial(
                    generate_transactions_pdf,
                    df_transactions, df_port,
                    valeur=_export_valeur, cash=_export_cash, total_apport=_export_apports_totaux,
                    performance=_export_performance, plus_value_latente=_export_plus_value_latente,
                    dividende_total=tot_dividends, frais_total=tot_fees,
                    broker_name=_export_pdf_broker,
                    pea_opening_date_str=_export_pdf_ouverture,
                ),
            )
            st.download_button(
                label="🧾 Exporter les données (PDF)",
                data=_export_pdf_bytes,
                file_name=f"ExportPDF_{_export_pdf_stamp}.pdf",
                mime="application/pdf",
                key="export_data_pdf_btn",
                use_container_width=True,
            )
            st.download_button(
                label="📄 Exporter les données (CSV)",
                data=df_transactions.to_csv(index=False).encode("utf-8-sig"),
                file_name=f"ExportCSV_{_export_xml_stamp}.csv",
                mime="text/csv",
                key="export_data_csv_btn",
                use_container_width=True,
            )

            st.markdown("---")
            st.markdown("**📥 Import (CSV ou Excel)**")
            st.caption("Formats acceptés : CSV, Excel (.xlsx, .xls). Le fichier doit avoir exactement les mêmes colonnes que l'export CSV.")
            st.warning(
                "⚠️ **L'import peut écraser tes données.** Avec « Remplacer entièrement », toutes tes transactions "
                "actuelles sont supprimées puis remplacées par le contenu du fichier. "
                "Fais d'abord un export CSV si tu veux une sauvegarde."
            )
            st.caption("Une fois le fichier envoyé, choisis l'option ci-dessous puis appuie sur le bouton « OK » qui apparaît juste en dessous.")
            _csv_uploaded = st.file_uploader(
                "Importer un fichier de transactions", type=["csv", "xlsx", "xls"], key="import_csv_uploader"
            )
            if _csv_uploaded is not None:
                try:
                    if _csv_uploaded.name.lower().endswith((".xlsx", ".xls")):
                        df_csv_import = pd.read_excel(_csv_uploaded)
                    else:
                        df_csv_import = pd.read_csv(_csv_uploaded)
                    _missing_cols = [c for c in _TRANSAC_COLUMNS if c not in df_csv_import.columns]
                    if _missing_cols:
                        st.error(f"Colonnes manquantes dans le fichier : {', '.join(_missing_cols)}")
                    else:
                        df_csv_import = df_csv_import[_TRANSAC_COLUMNS].copy()
                        df_csv_import["Date_Heure"] = pd.to_datetime(df_csv_import["Date_Heure"])
                        df_csv_import["Date_Rompus"] = pd.to_datetime(
                            df_csv_import["Date_Rompus"], errors="coerce"
                        )
                        _n_new = len(df_csv_import)
                        _n_old = len(df_transactions)
                        st.write(f"📄 {_n_new} lignes détectées dans le fichier (tu as actuellement {_n_old} transactions enregistrées).")
                        _import_mode = st.radio(
                            "Que faire de ces lignes ?",
                            ["Ajouter à mes transactions existantes", "Remplacer entièrement mes transactions"],
                            key="import_csv_mode",
                        )
                        _is_add = _import_mode.startswith("Ajouter")
                        if _is_add:
                            st.info(
                                f"Les {_n_new} lignes seront ajoutées à tes {_n_old} transactions. "
                                "Si ce fichier vient de ton propre export, elles apparaîtront en double : "
                                "choisis plutôt « Remplacer entièrement »."
                            )
                        else:
                            st.error(
                                f"⚠️ Cela va ÉCRASER tes {_n_old} transactions actuelles : elles seront supprimées et "
                                f"remplacées par les {_n_new} lignes de ce fichier. Action définitive."
                            )
                        _btn_label = (
                            f"✅ OK — ajouter ces {_n_new} lignes" if _is_add
                            else f"✅ OK — écraser mes {_n_old} transactions"
                        )
                        if st.button(_btn_label, key="import_csv_confirm", type="primary", use_container_width=True):
                            if _import_mode.startswith("Ajouter"):
                                df_transactions_new = pd.concat(
                                    [df_transactions, df_csv_import], ignore_index=True
                                )
                            else:
                                df_transactions_new = df_csv_import
                            ok_save, err_save = save_transactions_csv(df_transactions_new)
                            if ok_save:
                                load_data.clear()
                                st.success(f"{len(df_csv_import)} transactions importées.")
                                st.rerun()
                            else:
                                st.error(err_save)
                except ImportError as e:
                    st.error(
                        "Lecture Excel impossible : il manque une bibliothèque sur le serveur "
                        "(ajoute `openpyxl` pour .xlsx, et `xlrd` pour .xls, dans requirements.txt). "
                        f"Détail : {e}"
                    )
                except Exception as e:
                    st.error(f"Erreur lors de la lecture du fichier : {e}")


# "Nouvelle opération" et "Simulation" regroupés dans une seule carte, désormais FIXÉE en bas de
# l'écran (voir la règle CSS ".st-key-sticky_ops_bar" tout en haut du fichier) : toujours
# visibles à l'écran, quel que soit l'endroit du dashboard où l'on a défilé, plutôt que
# disponibles uniquement tout en haut de la page.
@fragment_wrapper
def _ops_bar_fragment():
    col_new_op, col_sim_op = st.columns(2, gap="small")
    with col_new_op:
        with st.container(key="new_op_btn_wrap"):
            _new_clicked = st.button("➕ Nouvelle opération", type="primary", key="add_op_main_btn", use_container_width=True)
    with col_sim_op:
        with st.container(key="sim_op_btn_wrap"):
            _sim_clicked = st.button("🧪 Simulation", key="sim_op_main_btn", use_container_width=True)

    # Une seule fenêtre à la fois. La fenêtre « Nouvelle opération » est mémorisée comme « ouverte »
    # (st.session_state["_op_dialog_open"]) et ré-ouverte à chaque rechargement du script, tant que
    # l'utilisateur ne l'a pas fermée lui-même (croix) ou enregistré l'opération. Ainsi, quitter
    # l'onglet sur téléphone puis revenir ne la ferme plus.
    if _sim_clicked:
        st.session_state["_op_dialog_open"] = False
        with st.spinner("⏳ Ouverture du simulateur..."):
            dialog_simulation_operation()
    elif _new_clicked:
        if _DIALOG_SUPPORTS_DISMISS:
            st.session_state["_op_dialog_open"] = True
        with st.spinner("⏳ Ouverture du formulaire..."):
            dialog_saisie_operation()
    elif st.session_state.get("_op_dialog_open") and _DIALOG_SUPPORTS_DISMISS:
        dialog_saisie_operation()

with st.container(key="sticky_ops_bar", border=True):
    _ops_bar_fragment()


# Détection automatique des anomalies TTF (voir detect_ttf_anomalies_cached) : contrairement à
# l'ancienne alerte, déclenchée seulement au moment d'enregistrer une vente, ce contrôle
# s'applique à CHAQUE chargement de l'app sur TOUT l'historique des transactions — il détecte
# donc aussi bien un problème qui vient d'être créé qu'un problème déjà présent dans les
# transactions existantes. Chaque anomalie peut être masquée individuellement pour la session
# (elle réapparaîtra au prochain chargement tant que la transaction concernée n'est pas corrigée).
_ttf_anomalies = detect_ttf_anomalies(df_transactions)
_ttf_dismissed = st.session_state.get("_ttf_anomalies_dismissed", set())
_ttf_anomalies_visibles = [a for a in _ttf_anomalies if a["cle"] not in _ttf_dismissed]

for _anomalie in _ttf_anomalies_visibles:
    _ttf_avant = _anomalie["ttf_enregistre"]
    _ttf_apres = _anomalie["ttf_du"]
    _diff_ttf = round(_ttf_avant - _ttf_apres, 2)
    if _ttf_apres <= 0.005:
        _phrase_montant = "cette TTF ne sera donc finalement pas due."
    else:
        _phrase_montant = f"le montant réellement dû est donc de <b>{fmt_eur(_ttf_apres)}</b> (au lieu de <b>{fmt_eur(_ttf_avant)}</b>)."
    # Une ligne "👉 Pensez à modifier..." par achat concerné ce jour-là (autant de lignes que
    # d'heures d'achat distinctes), chacune avec le TTF avant/après propre à CETTE ligne d'achat
    # (et non le total agrégé de la journée).
    _lignes_action_html = "".join(
        f'<div style="font-size:0.82rem; color:#78350f; margin-top:6px;">👉 Pensez à modifier la ligne d\'achat du {_anomalie["date_str_dash"]} à {_l["heure_str"]} dans le détail des transactions : passez son champ TTF de <b>{fmt_eur(_l["ttf_avant_ligne"])}</b> à <b>{fmt_eur(_l["ttf_apres_ligne"])}</b>.</div>'
        for _l in _anomalie["lignes_ttf"]
    )
    st.markdown(
        f"""
        <div style="margin-top:10px; padding:14px 18px; background:#fefce8; border:1px solid #fde68a; border-left:4px solid #d97706; border-radius:10px;">
            <div style="font-size:0.85rem; font-weight:800; color:#92400e;">⚠️ TTF à corriger pour l'achat de {_anomalie['nom']} du {_anomalie['date_str_dash']} à {_anomalie['heures_str']} :</div>
            <div style="font-size:0.82rem; color:#78350f; margin-top:6px;">Vous avez acheté puis (en partie ou en totalité) revendu <b>{_anomalie['nom']}</b> le même jour ({_anomalie['date_str']}). La TTF n'est en réalité prélevée qu'une fois par jour, uniquement sur les titres éligibles encore détenus <b>en fin de journée</b> — {_phrase_montant}</div>
            {_lignes_action_html}
        </div>
        """,
        unsafe_allow_html=True
    )
    if st.button("Compris, masquer cet avertissement", key=f"btn_dismiss_ttf_{_anomalie['cle']}"):
        _ttf_dismissed = set(st.session_state.get("_ttf_anomalies_dismissed", set()))
        _ttf_dismissed.add(_anomalie["cle"])
        st.session_state["_ttf_anomalies_dismissed"] = _ttf_dismissed
        st.rerun()

# --- Alerte watchlist : valeurs suivies proches de leur zone d'achat (voir l'onglet
# "👁️ Watchlist"). Affichée ici, au même endroit que l'alerte TTF ci-dessus (avant même la
# création des onglets), pour être visible dès l'arrivée sur le dashboard — auparavant, elle
# n'apparaissait qu'après avoir ouvert l'onglet "Vue d'ensemble" et déplié son expander.
# N'affiche rien si la watchlist est vide ou si aucune valeur suivie n'a de zone d'achat
# définie, pour ne pas surcharger le haut du dashboard sans raison.
#
# Chaque valeur proche de sa zone a SA PROPRE petite alerte (comme les anomalies TTF
# ci-dessus, une carte par anomalie) avec SON PROPRE bouton "Compris, masquer cet
# avertissement" : la masquer ne fait donc disparaître QUE cette valeur-là pour la session
# (mémorisée dans st.session_state, comme les anomalies TTF), sans rien casser au reste de
# l'IHM — les autres alertes watchlist éventuelles, la Vue d'ensemble, les onglets, etc.
# continuent de s'afficher normalement. Elle réapparaîtra au prochain chargement de l'app
# tant que le prix reste dans la zone "proche". ---
_wl_items_overview = app_config.get("watchlist", [])
_wl_alertes = []
if _wl_items_overview:
    for _it_wl in _wl_items_overview:
        _zone_wl_ov = _it_wl.get("zone_achat")
        if not _zone_wl_ov:
            continue
        _prix_wl_ov = get_live_price(_it_wl["ticker"])
        if _prix_wl_ov is None:
            continue
        _ecart_wl_ov = (_prix_wl_ov - _zone_wl_ov) / _zone_wl_ov * 100
        if _ecart_wl_ov <= 3.0:  # même seuil que l'onglet Watchlist
            _wl_alertes.append((_it_wl["ticker"], _it_wl["nom"], _prix_wl_ov, _zone_wl_ov, _ecart_wl_ov))

_wl_alertes_dismissed = st.session_state.get("_wl_alertes_dismissed", set())
_wl_alertes_visibles = [a for a in _wl_alertes if a[0] not in _wl_alertes_dismissed]

for (_tick_wl, _nom_wl, _px_wl, _zn_wl, _ec_wl) in _wl_alertes_visibles:
    _phrase_wl = "déjà dans la zone" if _ec_wl <= 0 else f"à {_ec_wl:+.1f}".replace(".", ",") + " % de la zone"
    st.markdown(
        f'<div style="margin-top:10px; padding:14px 18px; background:#fefce8; '
        f'border:1px solid #fde68a; border-left:4px solid #d97706; border-radius:10px;">'
        f'<div style="font-size:0.85rem; font-weight:800; color:#92400e;">'
        f'{"🟢" if _ec_wl <= 0 else "🟡"} Watchlist — {_nom_wl} proche de sa zone d\'achat</div>'
        f'<div style="font-size:0.82rem; color:#78350f; margin-top:6px;">{_nom_wl} : {fmt_eur(_px_wl)} '
        f'({_phrase_wl}) — zone d\'achat {fmt_eur(_zn_wl)}</div>'
        f'</div>',
        unsafe_allow_html=True
    )
    if st.button("Compris, masquer cet avertissement", key=f"btn_dismiss_wl_{_tick_wl}"):
        _wl_alertes_dismissed = set(st.session_state.get("_wl_alertes_dismissed", set()))
        _wl_alertes_dismissed.add(_tick_wl)
        st.session_state["_wl_alertes_dismissed"] = _wl_alertes_dismissed
        st.rerun()

# Séparateur unique affiché uniquement s'il y a effectivement une (ou plusieurs) alerte(s)
# au-dessus (TTF et/ou watchlist) : sinon, il laissait un espace vide entre les boutons et le
# reste du dashboard, sans rien à séparer. Un seul séparateur pour les deux types d'alerte
# (et non un après chacun) : les mettre bout à bout créait deux barres vides collées l'une à
# l'autre, sans rien entre elles, dès que les deux types d'alerte étaient présents en même
# temps — d'où les "2 barres vides" repérées entre l'alerte et la Vue d'ensemble.
if "_swr_seen_epoch_history" not in st.session_state:
    st.session_state["_swr_seen_epoch_history"] = _epoch_now
elif st.session_state["_swr_seen_epoch_history"] != _epoch_now:
    _compute_ticker_daily_history_cached.clear()
    get_portfolio_history_cached.clear()
    st.session_state["_swr_seen_epoch_history"] = _epoch_now
history_df_global = get_portfolio_history(df_transactions)
poche_especes = 0.0
apports_totaux = df_transactions[df_transactions["Type"] == "APPORT"]["Quantité"].sum() - df_transactions[df_transactions["Type"] == "RETRAIT"]["Quantité"].sum()

if history_df_global is not None and not history_df_global.empty:
    poche_especes = history_df_global["Poche Espèces (€)"].iloc[-1]

tot_value_globale = tot_value_actions + poche_especes
global_pnl = tot_value_actions - tot_invested

df_divs_pure_calc = df_transactions[df_transactions["Type"] == "DIVIDENDE"].copy()
net_divs_total = 0.0
if not df_divs_pure_calc.empty:
    net_divs_total = (df_divs_pure_calc["Prix Unitaire (€)"] - df_divs_pure_calc["Commission (€)"].fillna(0) - df_divs_pure_calc["Retenue_Source_Etrangere"].fillna(0)).sum()

df_rompus_calc = df_transactions[(df_transactions["Type"] == "SPLIT") & (df_transactions["Rompu"] > 0)].copy()
if not df_rompus_calc.empty:
    # Un rompu dont la date de versement (Date_Rompus) est encore dans le futur n'a pas
    # réellement été crédité par le courtier : il ne doit donc pas encore être compté comme
    # "perçu", sous peine de gonfler ce total (et le solde espèces qui en découle) par rapport
    # au compte réel tant que le versement n'a pas eu lieu.
    _date_rompus_calc = df_rompus_calc["Date_Rompus"].fillna(df_rompus_calc["Date_Heure"]) if "Date_Rompus" in df_rompus_calc.columns else df_rompus_calc["Date_Heure"]
    net_divs_total += df_rompus_calc.loc[_date_rompus_calc <= _now_paris(), "Rompu"].sum()

total_gains_cumules = global_pnl + tot_realized_pnl + net_divs_total
# Dénominateur = capital total réellement engagé sur toute la durée de vie du portefeuille
# (achats cumulés), pas seulement le capital encore investi aujourd'hui. Sinon, une position
# entièrement soldée avec plus-value gonfle artificiellement le % (son gain reste compté au
# numérateur alors que son capital disparaît du dénominateur).
# Dénominateur = total des apports nets (argent réellement sorti de votre poche). C'est la
# seule base cohérente avec total_gains_cumules : par construction, Valeur totale actuelle -
# Apports nets = total_gains_cumules (identité comptable), donc c'est aussi la base que la
# plupart des courtiers utilisent pour leur "performance depuis l'ouverture". On ne retombe sur
# le capital investi que si aucun apport n'est enregistré (cas limite / données incomplètes).
base_perf_globale = apports_totaux if apports_totaux > 0 else (tot_cost_basis_global if tot_cost_basis_global > 0 else tot_invested)
perf_globale = (total_gains_cumules / base_perf_globale) * 100 if base_perf_globale > 0 else 0.0

perf_ytd = 0.0
perf_mois_en_cours = 0.0
perf_jour = 0.0
gain_total_yr = 0.0
gain_total_mo = 0.0
gain_total_j = 0.0

if history_df_global is not None and not history_df_global.empty:
    current_year = _now_paris().year
    current_month = _now_paris().month
    
    start_of_month_ts = pd.Timestamp(datetime(current_year, current_month, 1))
    start_ytd_ts = pd.Timestamp(datetime(current_year, 1, 1))
    
    def get_h_val_dashboard(ts):
        # Renvoie, en plus des 4 valeurs déjà utilisées ailleurs, la "Valeur Actions (€)" et le
        # "Capital Investi Total (€)" du point dans le temps demandé : ce sont ces deux colonnes
        # (hors trésorerie) qu'il faut utiliser pour isoler la plus-value LATENTE, car
        # "Valeur du Portefeuille (€)" inclut la poche espèces (qui contient déjà le produit des
        # ventes et des dividendes). Réutiliser "Valeur du Portefeuille" pour la partie latente
        # PUIS rajouter le réalisé/dividendes en plus revenait à les compter deux fois.
        if ts in history_df_global.index:
            row = history_df_global.loc[ts]
        else:
            idx = history_df_global.index[history_df_global.index <= ts]
            if len(idx) == 0:
                return 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
            row = history_df_global.loc[idx[-1]]
        return (
            row["Valeur du Portefeuille (€)"], row["Apports Cumulés (€)"],
            row["Gain Réalisé Cumulé (€)"], row["Dividendes Cumulés (€)"],
            row["Valeur Actions (€)"], row["Capital Investi Total (€)"],
        )

    today_ts = _today_paris()
    val_now, app_now, real_now, div_now, act_now, inv_now = get_h_val_dashboard(today_ts)

    val_mo_i, app_mo_i, real_mo_i, div_mo_i, act_mo_i, inv_mo_i = get_h_val_dashboard(start_of_month_ts - pd.Timedelta(seconds=1))
    net_real_mo = real_now - real_mo_i
    net_div_mo = div_now - div_mo_i
    net_latente_mo = (act_now - inv_now) - (act_mo_i - inv_mo_i)
    gain_total_mo = net_latente_mo + net_real_mo + net_div_mo
    base_denom_mo = val_mo_i if val_mo_i > 0 else (app_mo_i if app_mo_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
    if base_denom_mo > 0:
        perf_mois_en_cours = (gain_total_mo / base_denom_mo) * 100

    val_yr_i, app_yr_i, real_yr_i, div_yr_i, act_yr_i, inv_yr_i = get_h_val_dashboard(start_ytd_ts - pd.Timedelta(seconds=1))
    net_real_yr = real_now - real_yr_i
    net_div_yr = div_now - div_yr_i
    net_latente_yr = (act_now - inv_now) - (act_yr_i - inv_yr_i)
    gain_total_yr = net_latente_yr + net_real_yr + net_div_yr
    base_denom_yr = val_yr_i if val_yr_i > 0 else (app_yr_i if app_yr_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
    if base_denom_yr > 0:
        perf_ytd = (gain_total_yr / base_denom_yr) * 100

    val_veille, app_veille, real_veille, div_veille, act_veille, inv_veille = get_h_val_dashboard(today_ts - pd.Timedelta(days=1))
    net_real_j = real_now - real_veille
    net_div_j = div_now - div_veille
    net_latente_j = (act_now - inv_now) - (act_veille - inv_veille)
    gain_total_j = net_latente_j + net_real_j + net_div_j
    base_denom_j = val_veille if val_veille > 0 else (app_veille if app_veille > 0 else (tot_invested if tot_invested > 0 else 1.0))
    if base_denom_j > 0:
        perf_jour = (gain_total_j / base_denom_j) * 100

# Réglages d'affichage et bouton d'ajout déjà rendus plus haut (juste avant le calcul de
# l'historique, cf. commentaire à leur emplacement), pour garder l'ouverture du bouton rapide.
# Séparateur affiché uniquement s'il y avait effectivement une alerte (TTF et/ou watchlist)
# au-dessus (voir le commentaire à leur emplacement) : sinon, sans rien à séparer, il laissait
# un espace vide entre les boutons et le reste du dashboard.
if _ttf_anomalies_visibles or _wl_alertes_visibles:
    st.markdown("---")

# ==========================================
# CRÉATION DES ONGLETS NATIFS (st.tabs)
# ==========================================
# ------------------------------------------------------------------
# CHARGEMENT PARESSEUX DES ONGLETS
# Par défaut, Streamlit exécute le contenu de TOUS les onglets à CHAQUE interaction (validation
# d'une opération, changement de date...), même ceux qu'on ne regarde pas : sur ce dashboard,
# 10 onglets calculés et envoyés au navigateur à chaque rerun, dont l'onglet Historique
# (3 tableaux de plusieurs centaines de lignes stylées). Les versions récentes de Streamlit
# permettent de ne calculer QUE l'onglet affiché (st.tabs(..., on_change="rerun") + propriété
# .open) ; l'apparence reste celle des onglets natifs. Si la version installée est trop ancienne,
# on retombe automatiquement sur l'ancien comportement (tous les onglets calculés).
# Mettre _LAZY_TABS_ENABLED à False pour forcer l'ancien comportement.
# ------------------------------------------------------------------
_LAZY_TABS_ENABLED = True

# ------------------------------------------------------------------
# MÉMORISATION DU RENDU DES ONGLETS D'AFFICHAGE
# Les onglets Classements, Historique, Saisonnalité et Dividendes ne contiennent que de
# l'affichage (aucun widget dans la partie mémorisée) et ne dépendent que des transactions (et,
# pour Dividendes, du tableau des positions), de l'option « masquer les montants » et de la date
# du jour. Leur rendu est donc mémorisé par Streamlit (st.cache_data rejoue les éléments déjà
# construits : graphiques, tableaux) : revenir sur l'onglet, ou toute interaction pendant qu'il
# est ouvert, ne recalcule plus rien tant que ces entrées ne changent pas. La mémoire expire
# après 5 minutes (comme les cours de bourse sous-jacents) et dès qu'une transaction change.
# Mettre _RENDER_CACHE_ENABLED à False pour désactiver cette mémorisation.
# ------------------------------------------------------------------
_RENDER_CACHE_ENABLED = True

def _cache_render(fn):
    if not _RENDER_CACHE_ENABLED:
        return fn
    _cached_fn = st.cache_data(show_spinner=False, ttl=300, max_entries=4)(fn)

    def _run(*args, **kwargs):
        try:
            return _cached_fn(*args, **kwargs)
        except Exception as _exc:
            # Si Streamlit ne sait pas empreinter un argument ou mémoriser le résultat, on
            # exécute simplement le rendu normalement (sans mémorisation) plutôt que de planter.
            if type(_exc).__name__ in ("UnhashableParamError", "UnserializableReturnValueError"):
                return fn(*args, **kwargs)
            raise
    return _run

_TABS_LAZY = False
try:
    import inspect as _inspect
    _tabs_params = _inspect.signature(st.tabs).parameters
    _TABS_LAZY = _LAZY_TABS_ENABLED and ("on_change" in _tabs_params) and ("key" in _tabs_params)
except Exception:
    _TABS_LAZY = False

_TAB_LABELS = [
    "📊 Vue d'ensemble & Objectif",
    "📌 Positions & Transactions",
    "💰 Apports",
    "🏆 Classements",
    "🗓️ Saisonnalité",
    "📈 Performances & Indices",
    "📅 Historique",
    "💶 Dividendes & Cartographie",
    "🔍 Frais",
    "👁️ Watchlist",
    "🧮 Simulateurs"
]
if _TABS_LAZY:
    _tabs_created = st.tabs(_TAB_LABELS, on_change="rerun", key="main_tabs")
else:
    _tabs_created = st.tabs(_TAB_LABELS)
tab_overview, tab_positions, tab_apports, tab_classements, tab_saisonnalite, tab_perf, tab_history, tab_dividends, tab_fees, tab_watchlist, tab_simulateur = _tabs_created

def _tab_open(_tab):
    """True si le contenu de l'onglet doit être calculé : onglet actuellement affiché, ou
    chargement paresseux indisponible (.open absent ou None => on calcule, comme avant)."""
    return getattr(_tab, "open", None) is not False

# Streamlit oublie la valeur d'un widget quand il n'est pas affiché pendant un rerun. Avec des
# onglets paresseux, les widgets des onglets non affichés seraient donc réinitialisés (filtres,
# dates, montants saisis dans les simulateurs...) à chaque changement d'onglet. Pour l'éviter,
# on réaffecte leur valeur à chaque rerun pour les onglets NON affichés (technique documentée
# de conservation de l'état). Les clés ci-dessous sont extraites automatiquement du code de
# chaque onglet (widgets ayant un key= littéral).
_TAB_STATE_KEYS = {
    "tab_overview": ("k_objectif_cible", "k_objectif_date_fin", "k_objectif_perf", ),
    "tab_apports": (),
    "tab_positions": ("k_periode_tx", "tx_filter_start", "tx_filter_end", "tx_filter_actions", "tx_filter_types", "tx_filter_montant_min", "tx_filter_montant_max", "act_choice_radio", ),
    "tab_classements": ("k_periode_classements", ),
    "tab_perf": ("k_periode_perf", "k_perf_graph_date_debut", "k_perf_graph_date_fin", "multiselect_indices_benchmarks", ),
    "tab_watchlist": ("wl_mgmt_select", "k_wl_zone", "wl_mgmt_action", "k_wl_nom", "k_wl_nom_new", "k_wl_ticker_placeholder", "k_wl_ticker_new", ),
    "tab_simulateur": ("k_horizon_projection", "k_apport_mensuel_projection", "k_perf_annuelle_projection", "k_sim_retrait_montant", "k_sim_retrait_taux_ps", "k_sim_retrait_pea_5ans", "k_rp_depart", "k_rp_impot", "k_rp_retrait", "k_rp_infl", ),
}
_tab_objs_by_name = {
    "tab_overview": tab_overview, "tab_positions": tab_positions, "tab_apports": tab_apports, "tab_classements": tab_classements,
    "tab_saisonnalite": tab_saisonnalite, "tab_perf": tab_perf, "tab_history": tab_history,
    "tab_dividends": tab_dividends, "tab_fees": tab_fees, "tab_watchlist": tab_watchlist,
    "tab_simulateur": tab_simulateur,
}
if _TABS_LAZY:
    for _name_ka, _tab_ka in _tab_objs_by_name.items():
        if not _tab_open(_tab_ka):
            for _key_ka in _TAB_STATE_KEYS.get(_name_ka, ()):
                try:
                    if _key_ka in st.session_state:
                        st.session_state[_key_ka] = st.session_state[_key_ka]
                except Exception:
                    pass

# ------------------------------------------
# ONGLÊT 1 : VUE D'ENSEMBLE & OBJECTIF
# ------------------------------------------
if _tab_open(tab_overview):
    with tab_overview:
        _inject_metric_tips()
        with st.expander("📊 Vue d'ensemble du Portefeuille", expanded=True):
            # Conteneurs RÉELS (st.container(key=...), même mécanisme que les encadrés rouges
            # _req_field un peu plus haut dans le fichier) plutôt que des <div> ouverts dans un
            # st.markdown et "fermés" dans un autre : ces derniers ne s'enveloppaient en réalité
            # JAMAIS autour du contenu qui suivait (chaque st.markdown est injecté dans son propre
            # bloc HTML isolé, donc un <div> laissé ouvert s'auto-referme aussitôt sans rien
            # contenir) — ce qui produisait deux rectangles vides et sans contenu, juste posés là
            # avec leur fond de couleur et leur padding : un rectangle blanc (fond de
            # "dashboard-card") juste sous le titre de l'expander, et un rectangle bleuté (fond de
            # "row-capital-wrap") juste sous "Capital & Investissement", avant les vraies valeurs.
            # Avec un vrai st.container(key=...), le fond et le padding s'appliquent cette fois
            # autour du contenu qu'il contient réellement, et ces rectangles vides disparaissent.
            with st.container(key="dashboard_overview_card"):
                st.markdown("<p class='dashboard-section-title'>💰 Capital & Investissement</p>", unsafe_allow_html=True)
                with st.container(key="row_capital_wrap"):
                    r1_c1, r1_c2, r1_c3, r1_c4 = st.columns(4)
                    r1_c1.metric("Valeur Actuelle", fmt_eur(tot_value_globale))
                    r1_c2.metric("Montant Investi", fmt_eur(tot_invested))
                    r1_c3.metric("Cash Disponible", fmt_eur(poche_especes))
                    r1_c4.metric("Total Apports", fmt_eur(apports_totaux))

                st.markdown("<p class='dashboard-section-title' style='margin-top: 16px;'>📈 Performances</p>", unsafe_allow_html=True)
                with st.container(key="row_perf_wrap"):
                    _delta = lambda g: f"{g:+,.2f} €".replace(",", " ").replace(".", ",")
                    # Performance annuelle moyenne : performance globale ramenée à un taux annuel composé
                    # (indisponible tant que l'historique fait moins de 3 mois).
                    _ans_pea = max((_now_paris() - pea_opening_dt).days / 365.25, 0.0) if not df_transactions.empty else 0.0
                    if _ans_pea >= 0.25 and (1 + perf_globale / 100) > 0:
                        _perf_an_moy = ((1 + perf_globale / 100) ** (1 / _ans_pea) - 1) * 100
                        _perf_an_txt = fmt_perf_text_only(_perf_an_moy)
                    else:
                        _perf_an_txt = "N/A"
                    # 3 rangées de 2 : Globale | YTD ; Mois | Jour ; Perf. annuelle moyenne | Drawdown maximum.
                    r2_c1, r2_c2 = st.columns(2)
                    r2_c1.metric("Performance Globale", fmt_perf_text_only(perf_globale), delta=_delta(total_gains_cumules))
                    r2_c2.metric("Performance YTD", fmt_perf_text_only(perf_ytd), delta=_delta(gain_total_yr))
                    r2b_c1, r2b_c2 = st.columns(2)
                    r2b_c1.metric("Performance du Mois", fmt_perf_text_only(perf_mois_en_cours), delta=_delta(gain_total_mo))
                    r2b_c2.metric("Performance du Jour", fmt_perf_text_only(perf_jour), delta=_delta(gain_total_j))
                    # Gain moyen par an en € (gain total cumulé ramené à une année), affiché sur la flèche.
                    _gain_an_moy = (total_gains_cumules / _ans_pea) if _ans_pea >= 0.25 else None
                    # Drawdown : plus forte baisse depuis un sommet de la performance quotidienne (flux d'apports exclus).
                    _dd_max, _dd_cur = None, None
                    try:
                        _hd = history_df_global
                        if _hd is not None and len(_hd) >= 3:
                            _v = _hd["Valeur du Portefeuille (€)"].astype(float)
                            _a = _hd["Apports Cumulés (€)"].astype(float)
                            _prev = _v.shift(1)
                            _r = ((_v - _prev - _a.diff().fillna(0.0)) / _prev).where(_prev > 0).fillna(0.0)
                            _idx = (1.0 + _r).cumprod()
                            _peak = np.maximum(_idx.cummax(), 1.0)
                            _dd = (_idx / _peak - 1.0) * 100.0
                            _dd_max, _dd_cur = float(_dd.min()), float(_dd.iloc[-1])
                    except Exception:
                        _dd_max, _dd_cur = None, None
                    r2c_c1, r2c_c2 = st.columns(2)
                    r2c_c1.metric("Performance Annuelle Moyenne", _perf_an_txt,
                                  delta=(_delta(_gain_an_moy) if _gain_an_moy is not None else None))
                    r2c_c2.metric("Drawdown Maximum",
                                  (fmt_perf_text_only(min(_dd_max, 0.0)) if _dd_max is not None else "N/A"),
                                  delta=(f"{_dd_cur:.2f}%".replace(".", ",") if _dd_cur is not None else None))

                st.markdown("<p class='dashboard-section-title' style='margin-top: 16px;'>🏷️ Plus-values, Dividendes & Frais</p>", unsafe_allow_html=True)
                with st.container(key="row_gains_wrap"):
                    r3_c1, r3_c2 = st.columns(2)
                    # Plus-Value Latente : gain latent rapporté au capital actuellement investi dans les
                    # actions détenues (tot_invested = PRU × quantités en portefeuille aujourd'hui).
                    pct_latente = (global_pnl / tot_invested * 100) if tot_invested > 0 else 0.0
                    # Plus-Value Actée : gain déjà réalisé rapporté à la valeur totale actuelle du
                    # portefeuille (actions + poche espèces).
                    pct_actee = (tot_realized_pnl / tot_value_globale * 100) if tot_value_globale > 0 else 0.0
                    r3_c1.metric("Plus-Value Latente", fmt_eur(global_pnl), delta=(f"{pct_latente:+,.2f}%".replace(",", " ").replace(".", ",")))
                    r3_c2.metric("Plus-Value Actée", fmt_eur(tot_realized_pnl), delta=(f"{pct_actee:+,.2f}%".replace(",", " ").replace(".", ",")))
                    r3b_c1, r3b_c2 = st.columns(2)
                    # % pertinent pour les dividendes et les frais : rapportés au total des apports nets (l'argent
                    # réellement sorti de la poche), comme la performance globale -> directement comparables entre eux.
                    pct_div_apports = (net_divs_total / apports_totaux * 100) if apports_totaux > 0 else None
                    pct_frais_apports = (tot_fees / total_gains_cumules * 100) if total_gains_cumules > 0 else None
                    r3b_c1.metric("Dividendes Reçus", fmt_eur(net_divs_total),
                                  delta=(f"{pct_div_apports:+,.2f}%".replace(",", " ").replace(".", ",") if pct_div_apports is not None else None))
                    r3b_c2.metric("Frais Totaux", fmt_eur(tot_fees),
                                  delta=(f"{pct_frais_apports:.2f}%".replace(".", ",") if pct_frais_apports is not None else None),
                                  delta_color="inverse")

                    # Rendements des dividendes : dividendes nets annuels (reçus ÷ années depuis l'ouverture, après
                    # 3 mois) rapportés soit à la valeur actuelle des titres (cours), soit à leur coût de revient (PRU).
                    _ans_div = max((_now_paris() - pea_opening_dt).days / 365.25, 0.0) if not df_transactions.empty else 0.0
                    _div_annuel = (net_divs_total / _ans_div) if _ans_div >= 0.25 else net_divs_total
                    _rend_cours_txt = f"{_div_annuel / tot_value_actions * 100:.2f} %".replace(".", ",") if tot_value_actions > 0 else "N/A"
                    _rend_cout_txt = f"{_div_annuel / tot_invested * 100:.2f} %".replace(".", ",") if tot_invested > 0 else "N/A"
                    # Dividendes moyens perçus par an en € (sur la flèche), comme les autres montants.
                    _div_an_moy = (net_divs_total / _ans_div) if _ans_div >= 0.25 else None
                    r3c_c1, r3c_c2 = st.columns(2)
                    r3c_c1.metric("Rendement sur cours", _rend_cours_txt,
                                  delta=(_delta(_div_an_moy) if _div_an_moy is not None else None))
                    r3c_c2.metric("Rendement sur coût", _rend_cout_txt,
                                  delta=(_delta(_div_an_moy) if _div_an_moy is not None else None))

        # --- Alerte watchlist : valeurs suivies proches de leur zone d'achat (voir l'onglet
        # "👁️ Watchlist"). Déplacée au-dessus de "Vue d'ensemble du Portefeuille", au même endroit
        # que l'alerte TTF ci-dessus (voir plus haut dans le script) : elle est ainsi visible dès
        # l'arrivée sur le dashboard, avant même d'ouvrir un onglet, comme n'importe quelle autre
        # alerte de ce type. N'affiche rien si la watchlist est vide ou si aucune valeur suivie n'a de
        # zone d'achat définie, pour ne pas surcharger le haut du dashboard sans raison. ---
        with st.expander("🎯 Objectif", expanded=True):
            # Trois valeurs saisies par l'opérateur et enregistrées dans la config dès qu'elles changent :
            # valeur totale visée, date de fin et performance annuelle attendue -> apport mensuel nécessaire.
            _cur_target = int(app_config.get("yearly_target", 10000))
            try:
                _cur_fin = pd.Timestamp(str(app_config.get("objectif_fin") or "")).date()
            except Exception:
                _cur_fin = date(_today_paris().year, 12, 31)
            try:
                _cur_perf = float(app_config.get("objectif_perf", 7.0))
            except Exception:
                _cur_perf = 7.0

            def _sauver_objectif():
                _t = int(st.session_state.get("k_objectif_cible", _cur_target))
                _f = st.session_state.get("k_objectif_date_fin", _cur_fin)
                _p = float(st.session_state.get("k_objectif_perf", _cur_perf))
                app_config["yearly_target"] = _t
                app_config["objectif_fin"] = _f.strftime("%Y-%m-%d")
                app_config["objectif_perf"] = _p
                _ok, _err = save_config(app_config)
                if not _ok:
                    st.session_state["_objectif_save_err"] = _err

            with st.container(border=True):
                st.markdown("**💰 Objectif**")
                with st.container(key="compact_cols_objectif"):
                    _c1, _c2, _c3 = st.columns(3)
                    _in_target = _c1.number_input("Valeur visée (€)", min_value=0, step=1, value=_cur_target, format="%d",
                                                  key="k_objectif_cible", on_change=_sauver_objectif)
                    _in_fin = _c2.date_input("Date de fin", value=_cur_fin, min_value=date(2000, 1, 1), max_value=date(2100, 12, 31),
                                             format="DD/MM/YYYY", key="k_objectif_date_fin", on_change=_sauver_objectif)
                    _in_perf = _c3.number_input("Performance / an (%)", min_value=-50.0, max_value=100.0, value=_cur_perf,
                                                step=0.5, format="%.1f", key="k_objectif_perf", on_change=_sauver_objectif)
                if st.session_state.get("_objectif_save_err"):
                    st.warning(st.session_state.pop("_objectif_save_err"))

            def _obj_card(label, value, color, big=False):
                return (f'<div style="background:{color}14; border:1px solid {color}55; border-radius:12px; padding:8px 4px; '
                        'text-align:center; min-width:0; display:flex; flex-direction:column; justify-content:center;">'
                        f'<div style="font-size:min({"0.74rem" if big else "0.68rem"},{"2.9vw" if big else "2.6vw"}); color:#64748b; text-transform:uppercase; font-weight:700; '
                        f'letter-spacing:0.03em; line-height:1.25;">{label}</div>'
                        f'<div style="font-size:min({"1.3rem" if big else "1.1rem"},{"5vw" if big else "4vw"}); font-weight:800; color:{color}; margin-top:3px; line-height:1.25;">{value}</div></div>')
            _grid = "display:grid; gap:6px; margin-top:8px;"

            _jours_obj = (pd.Timestamp(_in_fin) - pd.Timestamp(_today_paris())).days
            _v0 = float(tot_value_globale)
            _prog = max(0.0, min((_v0 / _in_target * 100) if _in_target > 0 else 0.0, 100.0))
            if int(_in_target) <= 0:
                st.info("Renseignez une valeur visée supérieure à 0.")
            elif _jours_obj < 15:
                st.info("La date de fin est trop proche (ou dépassée) pour calculer un apport mensuel.")
            else:
                _n = _jours_obj / 30.4375                                   # mois restants
                _rm = (1.0 + float(_in_perf) / 100.0) ** (1.0 / 12.0) - 1.0   # taux mensuel équivalent
                _g = (1.0 + _rm) ** _n
                _sans_apport = _v0 * _g                                      # valeur à la date visée sans nouvel apport
                _manque = float(_in_target) - _sans_apport
                if _manque <= 0:
                    _pmt = 0.0
                elif abs(_rm) < 1e-9:
                    _pmt = _manque / _n
                else:
                    _pmt = _manque * _rm / (_g - 1.0)
                if _pmt <= 0:
                    _coul, _bandeau = "#15803d", "🎉 Objectif atteint sans nouvel apport"
                    _grad = "linear-gradient(90deg, #15803d, #22c55e)"
                else:
                    # Palette selon l'effort demandé : apport mensuel rapporté à la valeur visée (par mois).
                    _effort = _pmt / float(_in_target) * 100
                    if _effort <= 0.5:
                        _coul, _bandeau, _grad = "#16a34a", "🌊 Effort léger", "linear-gradient(90deg, #16a34a, #4ade80)"
                    elif _effort <= 1.5:
                        _coul, _bandeau, _grad = "#4d7c0f", "🚀 Effort raisonnable", "linear-gradient(90deg, #65a30d, #a3e635)"
                    elif _effort <= 3.0:
                        _coul, _bandeau, _grad = "#d97706", "⚡ Effort soutenu", "linear-gradient(90deg, #f59e0b, #fbbf24)"
                    else:
                        _coul, _bandeau, _grad = "#dc2626", "🔥 Effort important", "linear-gradient(90deg, #dc2626, #f87171)"
                st.markdown(
                    _progress_bar_html(_prog, _grad, _coul, f"{_prog:.1f} % de l'objectif".replace(".", ","))
                    + f'<div style="{_grid} grid-template-columns:repeat(2,minmax(0,1fr));">'
                    + _obj_card("Apport mensuel nécessaire", fmt_eur(_pmt), _coul, big=True)
                    + _obj_card("Niveau d'effort", _bandeau, _coul, big=True)
                    + '</div>'
                    + f'<div style="{_grid} grid-template-columns:repeat(3,minmax(0,1fr));">'
                    + _obj_card("Actuel", fmt_eur(_v0), "#0284c7")
                    + _obj_card("Total à verser", fmt_eur(_pmt * _n), "#4f46e5")
                    + _obj_card("Sans nouvel apport", fmt_eur(_sans_apport), "#64748b")
                    + '</div>'
                    + '<div style="height:22px;"></div>',   # ligne vide avant le bas de la section
                    unsafe_allow_html=True,
                )

# ------------------------------------------
# ONGLÊT 2 : POSITIONS & TRANSACTIONS
# ------------------------------------------
if _tab_open(tab_positions):
    with tab_positions:
        df_active = df_port[df_port["Quantité"] > 0.0001] if not df_port.empty else pd.DataFrame()

        with st.expander("📌 Détail des Positions Actives", expanded=True):
            if not df_active.empty:
                # Variation du jour par titre (cours en direct vs dernière clôture AVANT aujourd'hui),
                # à partir de l'historique déjà préchargé (même date de départ que le préchargement).
                def _var_jour_ticker(ticker):
                    try:
                        if not _start_date_str_precharge:
                            return None
                        h = get_ticker_history(ticker, _start_date_str_precharge)
                        if h is None or h.empty or "Close" not in h.columns:
                            return None
                        cl = h["Close"].dropna()
                        if cl.empty:
                            return None
                        if getattr(cl.index, "tz", None) is not None:
                            cl.index = cl.index.tz_localize(None)
                        cl.index = cl.index.normalize()
                        avant = cl[cl.index < _today_paris()]
                        ref = avant.iloc[-1] if not avant.empty else cl.iloc[-1]
                        px = get_live_price(ticker)
                        if px is None or not ref:
                            return None
                        return float(px - ref), float((px - ref) / ref * 100)
                    except Exception:
                        return None

                df_active = df_active.copy()
                _vj = {t: _var_jour_ticker(t) for t in df_active["Ticker"]}
                df_active["Var Jour (€)"] = [
                    (_vj[t][0] * q) if _vj.get(t) else np.nan for t, q in zip(df_active["Ticker"], df_active["Quantité"])
                ]
                df_active["Var Jour (%)"] = [(_vj[t][1]) if _vj.get(t) else np.nan for t in df_active["Ticker"]]
                df_active["Ancienneté (jours)"] = df_active["Jours Détention"] if "Jours Détention" in df_active.columns else np.nan
                # PRU ajusté : capital encore investi, diminué des dividendes perçus et des plus-values déjà
                # actées sur la ligne (ventes), rapporté à la quantité détenue.
                _gains_recup = df_active["Dividendes Reçus (€)"].fillna(0) + df_active["Gain Réalisé (€)"].fillna(0)
                _pru_aj = (df_active["Capital Investi (€)"] - _gains_recup) / df_active["Quantité"].replace(0, np.nan)
                df_active["PRU ajusté"] = [
                    "N/A" if pd.isna(pa) else fmt_price_dynamic(max(pa, 0.0)) for pa in _pru_aj
                ]
                # Performance par rapport au PRU ajusté (np.inf = ligne entièrement « gratuite »).
                df_active["Perf. PRU ajusté (%)"] = [
                    np.nan if (pd.isna(pa) or pd.isna(px)) else (np.inf if pa <= 0 else (px - pa) / pa * 100)
                    for pa, px in zip(_pru_aj, df_active["Prix Actuel (€)"])
                ]
                df_active["Perf. annuelle moy. (%)"] = [
                    _perf_annualisee(pf, j) for pf, j in zip(df_active["Performance Active (%)"], df_active["Jours Détention"])
                ]
                df_active["Détention (jour)"] = [
                    _fmt_duree_detention(j, sec) for j, sec in zip(df_active["Jours Détention"], df_active["Secondes Détention"])
                ]

                cols_to_keep = [
                    'Nom', 'Quantité', 'PRU Net (€)', 'Prix Actuel (€)',
                    'Var Jour (%)',
                    'Valeur Actuelle (€)', 'Gain Latent (€)', 'Performance Active (%)',
                    'Gain Réalisé (€)', 'Dividendes Reçus (€)',
                    'PRU ajusté', 'Perf. PRU ajusté (%)', 'Détention (jour)', 'Perf. annuelle moy. (%)'
                ]

                existing_cols = [c for c in cols_to_keep if c in df_active.columns]
                df_active_table = df_active[existing_cols].copy()

                rename_mapping = {
                    'Prix Actuel (€)': 'Prix actuel (€)',
                    'Valeur Actuelle (€)': 'Valeur Actuel (€)',
                    'Dividendes Reçus (€)': 'Dividende Reçu (€)',
                    'Var Jour (%)': 'Variation jour (%)',
                    'Performance Active (%)': 'Performance (%)'
                }
                df_active_fmt = df_active_table.rename(columns=rename_mapping)
            
                if "Performance (%)" in df_active_fmt.columns:
                    df_active_fmt = df_active_fmt.sort_values(by="Performance (%)", ascending=False)
            
                if "Quantité" in df_active_fmt.columns:
                    def clean_qty_display(q):
                        if q % 1 == 0:
                            return f"{int(q):,}".replace(",", " ")
                        else:
                            return f"{q:,.4f}".replace(",", " ").rstrip("0").rstrip(",")
                    df_active_fmt["Quantité"] = df_active_fmt["Quantité"].apply(clean_qty_display)

                if "PRU Net (€)" in df_active_fmt.columns:
                    df_active_fmt["PRU Net (€)"] = df_active_fmt["PRU Net (€)"].apply(lambda x: fmt_price_dynamic(x))
                if "Prix actuel (€)" in df_active_fmt.columns:
                    # Variation du jour en % entre parenthèses, à côté du prix actuel.
                    _vj_pct_col = df_active_fmt["Variation jour (%)"] if "Variation jour (%)" in df_active_fmt.columns else None
                    df_active_fmt["Prix actuel (€)"] = [
                        fmt_price_dynamic(px) + ("" if (_vj_pct_col is None or pd.isna(vp)) else f" ({fmt_perf(vp)})")
                        for px, vp in zip(df_active_fmt["Prix actuel (€)"], _vj_pct_col if _vj_pct_col is not None else [np.nan] * len(df_active_fmt))
                    ]
                    if _vj_pct_col is not None:
                        df_active_fmt = df_active_fmt.drop(columns=["Variation jour (%)"])

                for col in ["Valeur Actuel (€)", "Dividende Reçu (€)"]:
                    if col in df_active_fmt.columns:
                        df_active_fmt[col] = df_active_fmt[col].apply(lambda x: fmt_eur(x))
                for col in ["Gain Latent (€)", "Gain Réalisé (€)"]:
                    if col in df_active_fmt.columns:
                        df_active_fmt[col] = df_active_fmt[col].apply(lambda x: fmt_eur_arrow(x))

                if "Performance (%)" in df_active_fmt.columns:
                    df_active_fmt["Performance (%)"] = df_active_fmt["Performance (%)"].apply(lambda x: fmt_perf(x))

                if "Perf. PRU ajusté (%)" in df_active_fmt.columns:
                    df_active_fmt["Perf. PRU ajusté (%)"] = df_active_fmt["Perf. PRU ajusté (%)"].apply(
                        lambda x: "Gratuite" if (not pd.isna(x) and np.isinf(x)) else fmt_perf(x))
                if "Perf. annuelle moy. (%)" in df_active_fmt.columns:
                    df_active_fmt["Perf. annuelle moy. (%)"] = df_active_fmt["Perf. annuelle moy. (%)"].apply(fmt_perf)

                # Affichage de toutes les lignes sans barre de scroll (height dynamique selon le nombre de lignes)
                row_height = 35
                header_height = 40
                total_height = header_height + (len(df_active_fmt) + 1) * row_height + 20  # +1 ligne : le Total
                _cols_fleche_active = [c for c in ["Performance (%)", "Perf. PRU ajusté (%)", "Perf. annuelle moy. (%)", "Gain Latent (€)", "Gain Réalisé (€)"]
                                       if c in df_active_fmt.columns]
                def _style_prix_actif(v):
                    sv = str(v)
                    if "(▲" in sv:
                        return "color:#16a34a; font-weight:700;"
                    if "(▼" in sv:
                        return "color:#dc2626; font-weight:700;"
                    return ""
                # Ligne Total (sommes sur les positions actives, calculées sur les valeurs numériques d'origine).
                # Performance et YoC : mêmes formules que par ligne, sur l'ensemble (gain latent / capital investi,
                # dividendes / capital investi).
                def _som_act(col):
                    if col not in df_active.columns:
                        return 0.0
                    return float(pd.to_numeric(df_active[col], errors="coerce").fillna(0).sum())
                _t_val, _t_gl, _t_gr = _som_act("Valeur Actuelle (€)"), _som_act("Gain Latent (€)"), _som_act("Gain Réalisé (€)")
                _t_div, _t_cap = _som_act("Dividendes Reçus (€)"), _som_act("Capital Investi (€)")
                _tot_act = {c: "" for c in df_active_fmt.columns}
                _tot_act["Nom"] = "Total"
                _tot_act["Valeur Actuel (€)"] = fmt_eur(_t_val)
                _tot_act["Gain Latent (€)"] = fmt_eur_arrow(_t_gl)
                _tot_act["Gain Réalisé (€)"] = fmt_eur_arrow(_t_gr)
                _tot_act["Dividende Reçu (€)"] = fmt_eur(_t_div)
                _tot_act["Performance (%)"] = fmt_perf(_t_gl / _t_cap * 100) if _t_cap > 0 else "N/A"
                # Perf. sur PRU ajusté (ensemble) : valeur actuelle vs capital net des dividendes et gains actés.
                _t_cout_aj = _t_cap - _t_div - _t_gr
                if _t_cap > 0:
                    _tot_act["Perf. PRU ajusté (%)"] = fmt_perf((_t_val - _t_cout_aj) / _t_cout_aj * 100) if _t_cout_aj > 0 else "Gratuite"
                    _jw = float((df_active["Jours Détention"].fillna(0) * df_active["Capital Investi (€)"].fillna(0)).sum()) / _t_cap
                    _tot_act["Perf. annuelle moy. (%)"] = fmt_perf(_perf_annualisee(_t_gl / _t_cap * 100, _jw))
                _t_vj = _som_act("Var Jour (€)")
                _t_val_veille = _t_val - _t_vj
                _tot_act["Prix actuel (€)"] = f"({fmt_perf(_t_vj / _t_val_veille * 100)})" if _t_val_veille > 0 else ""
                _EQ_COLS_ACTIVE = tuple(c for c in ("Gain Latent (€)", "Performance (%)", "Perf. PRU ajusté (%)", "Perf. annuelle moy. (%)") if c in df_active_fmt.columns)
                _tot_act = _dash_if_empty(pd.DataFrame([_tot_act]), eq_cols=_EQ_COLS_ACTIVE).iloc[0].to_dict()
                _html_table(
                    _dash_if_empty(df_active_fmt, eq_cols=_EQ_COLS_ACTIVE),
                    cell_style=lambda c, v: (_style_perf_cell(v) if c in _cols_fleche_active
                                             else ""),
                    max_height=min(max(total_height, 100), 1000),
                    total_row=_tot_act,
                    sticky_col="Nom",
                )
            else:
                st.info("Aucune position active pour le moment.")

        with st.expander("🥧 Répartition du portefeuille", expanded=True):
            _render_allocation(df_active, poche_especes)

        with st.expander("📜 Détail complet des transactions", expanded=True):
            if not df_transactions.empty:
                min_db_date = df_transactions["Date_Heure"].min().date() if pd.notnull(df_transactions["Date_Heure"].min()) else _today_paris().date()
                max_db_date = _today_paris().date()
            
                noms_actions_disponibles = sorted([
                    nom for nom in df_transactions["Nom"].dropna().unique() 
                    if nom != "Compte Courant"
                ])
                types_disponibles = [t for t in _OP_TYPE_LABELS.keys() if t in df_transactions["Type"].unique()]

                # Montant brut de chaque transaction (avant mise en forme), utilisé pour le filtre
                # "montant entre X et Y" ci-dessous. Même logique que calcul_montant plus bas, mais
                # renvoie un nombre au lieu d'une chaîne déjà formatée.
                def _montant_brut(row):
                    t = row["Type"]
                    try:
                        if t == "ACHAT":
                            return (row['Quantité'] * row['Prix Unitaire (€)']) + row['Frais Totaux (€)']
                        elif t == "VENTE":
                            return (row['Quantité'] * row['Prix Unitaire (€)']) - row['Frais Totaux (€)']
                        elif t in ["APPORT", "RETRAIT"]:
                            return row['Quantité']
                        elif t == "DIVIDENDE":
                            brut = row['Prix Unitaire (€)']
                            comm_div = row['Commission (€)']
                            ret_etr = row.get("Retenue_Source_Etrangere", 0.0)
                            arrondi_ctr = row.get("Arrondi_Courtier", 0.0)
                            arrondi_ctr = arrondi_ctr if pd.notnull(arrondi_ctr) else 0.0
                            return brut - comm_div - ret_etr + arrondi_ctr
                        elif t == "SPLIT":
                            return row['Rompu'] if pd.notnull(row['Rompu']) else 0.0
                        return 0.0
                    except Exception:
                        return 0.0

                _montants_bruts_all = df_transactions.apply(_montant_brut, axis=1)
                _montant_min_dispo = float(_montants_bruts_all.min()) if not _montants_bruts_all.empty else 0.0
                _montant_max_dispo = float(_montants_bruts_all.max()) if not _montants_bruts_all.empty else 0.0

                st.markdown("""
                <style>
                div[data-testid="stExpander"] .tx-filters-grid { margin-bottom: 4px; }
                </style>
            """, unsafe_allow_html=True)

                filtre_periode = st.selectbox(
                    "Période", _PERIODES_PRESETS + ["Période personnalisée"],
                    index=len(_PERIODES_PRESETS) - 1, key="k_periode_tx",
                )
                if filtre_periode == "Période personnalisée":
                    with st.container(key="compact_cols_tx_dates"):
                        c_f1, c_f2 = st.columns(2)
                        with c_f1:
                            filtre_debut = st.date_input("Du", value=min_db_date, min_value=min_db_date, max_value=max_db_date, format="DD-MM-YYYY", key="tx_filter_start")
                        with c_f2:
                            filtre_fin = st.date_input("Au", value=max_db_date, min_value=min_db_date, max_value=max_db_date, format="DD-MM-YYYY", key="tx_filter_end")
                else:
                    _deb_tx = periode_debut(filtre_periode)
                    filtre_debut = max(_deb_tx.date(), min_db_date) if _deb_tx is not None else min_db_date
                    filtre_fin = max_db_date

                with st.container(key="compact_cols_tx_filtres"):
                    c_f3, c_f4 = st.columns(2)
                    with c_f3:
                        filtre_actions = st.multiselect(
                            "Filtrer par action(s)",
                            options=noms_actions_disponibles,
                            default=[],
                            placeholder="Toutes les actions",
                            key="tx_filter_actions"
                        )
                    with c_f4:
                        filtre_types = st.multiselect(
                            "Filtrer par type(s)",
                            options=types_disponibles,
                            default=[],
                            placeholder="Tous les types",
                            format_func=lambda t: _OP_TYPE_LABELS.get(t, t),
                            key="tx_filter_types"
                        )

                    c_f5, c_f6 = st.columns(2)
                    with c_f5:
                        filtre_montant_min = st.number_input(
                            "Montant minimum (€)", value=None, step=10.0, format="%.2f",
                            placeholder=f"Depuis {fmt_eur(_montant_min_dispo)}", key="tx_filter_montant_min"
                        )
                    with c_f6:
                        filtre_montant_max = st.number_input(
                            "Montant maximum (€)", value=None, step=10.0, format="%.2f",
                            placeholder=f"Jusqu'à {fmt_eur(_montant_max_dispo)}", key="tx_filter_montant_max"
                        )
                st.markdown("<div style='margin-bottom: 8px;'></div>", unsafe_allow_html=True)

                mask_dates = (df_transactions["Date_Heure"].dt.date >= filtre_debut) & (df_transactions["Date_Heure"].dt.date <= filtre_fin)
                df_filtered_tx = df_transactions[mask_dates].copy()

                if filtre_actions:
                    df_filtered_tx = df_filtered_tx[df_filtered_tx["Nom"].isin(filtre_actions)]
                if filtre_types:
                    df_filtered_tx = df_filtered_tx[df_filtered_tx["Type"].isin(filtre_types)]
                if filtre_montant_min is not None or filtre_montant_max is not None:
                    _montants_bruts_filt = df_filtered_tx.apply(_montant_brut, axis=1)
                    if filtre_montant_min is not None:
                        df_filtered_tx = df_filtered_tx[_montants_bruts_filt >= filtre_montant_min]
                        _montants_bruts_filt = _montants_bruts_filt[_montants_bruts_filt >= filtre_montant_min]
                    if filtre_montant_max is not None:
                        df_filtered_tx = df_filtered_tx[_montants_bruts_filt <= filtre_montant_max]

                if not df_filtered_tx.empty:
                    df_display = df_filtered_tx.sort_values("Date_Heure", ascending=False).copy()
                    df_display["Date_Str"] = df_display["Date_Heure"].dt.strftime("%d-%m-%Y %H:%M:%S")
                
                    def format_type_col(row):
                        # Pour un SPLIT, le facteur saisi (stocké dans "Quantité") permet de
                        # distinguer automatiquement un vrai split (facteur > 1, ex. 11/10 chez Air
                        # Liquide) d'un regroupement d'actions (facteur < 1) : on l'affiche donc en
                        # clair au lieu du seul libellé générique "SPLIT".
                        if row["Type"] == "SPLIT":
                            facteur = row.get("Quantité")
                            if pd.notnull(facteur):
                                if facteur > 1:
                                    return "SPLIT"
                                elif facteur < 1:
                                    return "REGROUPEMENT"
                            return "SPLIT/REGROUPEMENT"
                        return row["Type"]

                    df_table = pd.DataFrame()
                    df_table["Date"] = df_display["Date_Str"]
                    df_table["Type"] = df_display.apply(format_type_col, axis=1)
                    df_table["Nom"] = df_display["Nom"]
                
                    def format_quantite(row):
                        if row["Type"] in ["APPORT", "RETRAIT"]:
                            return "N/A"
                        elif row["Type"] in ["ACHAT", "VENTE"]:
                            q = row['Quantité']
                            if q % 1 == 0:
                                return f"{int(q):,}".replace(",", " ")
                            return f"{q:,.4f}".replace(",", " ").rstrip("0").rstrip(",")
                        else:
                            q = row['Quantité']
                            if pd.notnull(q):
                                if q % 1 == 0:
                                    return f"{int(q):,}".replace(",", " ")
                                return f"{q:,.4f}".replace(",", " ").replace(".", ",")
                            return "N/A"

                    df_table["Quantité"] = df_display.apply(format_quantite, axis=1)
                
                    def format_prix(row):
                        if row["Type"] in ["APPORT", "RETRAIT"]:
                            return "N/A"
                        elif row["Type"] == "SPLIT":
                            rompu_val = row['Rompu']
                            if pd.notnull(rompu_val) and rompu_val > 0:
                                return f"{fmt_eur(rompu_val)} (Rompu)"
                            return "N/A"
                        else:
                            p_val = row['Prix Unitaire (€)']
                            if pd.notnull(p_val):
                                # La TTF n'est plus affichée ici (elle a sa propre place, détaillée
                                # dans la colonne "Frais" juste à côté) : on ne passe plus ttf_val.
                                return fmt_price_dynamic(p_val, None, None, include_comm=False)
                            return "N/A"

                    def format_frais(row):
                        total = row["Frais Totaux (€)"]
                        base = fmt_eur(total) if pd.notnull(total) and total > 0 else "0,00 €"
                        ttf_val = row.get('TTF (€)', 0.0)
                        if pd.notnull(ttf_val) and ttf_val > 0:
                            return f"{base} (Dont TTF : {fmt_eur(ttf_val)})"
                        return base

                    df_table["Prix"] = df_display.apply(format_prix, axis=1)
                    df_table["Frais"] = df_display.apply(format_frais, axis=1)
                
                    def calcul_montant(row):
                        t = row["Type"]
                        if t == "ACHAT":
                            return fmt_eur((row['Quantité'] * row['Prix Unitaire (€)']) + row['Frais Totaux (€)'])
                        elif t == "VENTE":
                            return fmt_eur((row['Quantité'] * row['Prix Unitaire (€)']) - row['Frais Totaux (€)'])
                        elif t in ["APPORT", "RETRAIT"]:
                            return fmt_eur(row['Quantité'])
                        elif t == "DIVIDENDE":
                            brut = row['Prix Unitaire (€)']
                            comm_div = row['Commission (€)']
                            ret_etr = row.get("Retenue_Source_Etrangere", 0.0)
                            arrondi_ctr = row.get("Arrondi_Courtier", 0.0)
                            arrondi_ctr = arrondi_ctr if pd.notnull(arrondi_ctr) else 0.0
                            net_recu = brut - comm_div - ret_etr + arrondi_ctr
                            return fmt_eur(net_recu)
                        elif t == "SPLIT":
                            r_val = row['Rompu'] if pd.notnull(row['Rompu']) else 0.0
                            return fmt_eur(r_val) if r_val > 0 else "N/A"
                        else:
                            return "N/A"

                    df_table["Montant"] = df_display.apply(calcul_montant, axis=1)
                    df_table.reset_index(drop=True, inplace=True)
                    total_rows = len(df_table)
                    df_table.index = total_rows - df_table.index
                
                    def color_transactions(row):
                        t = row["Type"] if "Type" in row else ""
                        if t == "ACHAT":
                            return ['background-color: #f0f7ff;'] * len(row)
                        elif t == "VENTE":
                            return ['background-color: #fdf2f2;'] * len(row)
                        elif t == "DIVIDENDE":
                            return ['background-color: #f2fcf5;'] * len(row)
                        elif t == "APPORT":
                            return ['background-color: #e6f4ea;'] * len(row)
                        elif t == "RETRAIT":
                            return ['background-color: #f5f3ff;'] * len(row)
                        elif t in ("SPLIT", "REGROUPEMENT", "SPLIT/REGROUPEMENT"):
                            return ['background-color: #fff7ed;'] * len(row)
                        return [''] * len(row)

                    _bg_tx = {"ACHAT": "#f0f7ff", "VENTE": "#fdf2f2", "DIVIDENDE": "#f2fcf5", "APPORT": "#e6f4ea",
                              "RETRAIT": "#f5f3ff", "SPLIT": "#fff7ed", "REGROUPEMENT": "#fff7ed", "SPLIT/REGROUPEMENT": "#fff7ed"}
                    _row_styles_tx = [f"background-color: {_bg_tx[t]};" if t in _bg_tx else "" for t in df_table["Type"]]
                    _html_table(_dash_if_empty(df_table), row_styles=_row_styles_tx, show_index=True, index_label="N°", max_height=350)
                else:
                    st.info("Aucune transaction trouvée avec ces critères.")

                @fragment_wrapper
                def _gestion_transactions_fragment():
                    # Isole tout ce bloc (sélection d'une transaction, bascule Modifier/Supprimer,
                    # formulaire d'édition) dans un st.fragment : sans cela, CHAQUE interaction ici
                    # (choisir une transaction, cliquer sur la petite croix du selectbox pour
                    # annuler la sélection, changer le radio Modifier/Supprimer, remplir un champ du
                    # formulaire) relançait TOUT le script, y compris les cours en direct (yfinance)
                    # et tout l'historique du portefeuille tout en haut du fichier — d'où la lenteur
                    # ressentie. Avec le fragment, seules ces interactions redéclenchent ce bloc ;
                    # le st.rerun() explicite après un enregistrement réussi continue, lui, à
                    # relancer toute l'application (nécessaire pour rafraîchir totaux/graphiques).
                    global df_transactions
                    st.markdown("#### 🛠️ Gestion des transactions (Modifier / Supprimer)")
                    df_display_mgmt = df_transactions.sort_values("Date_Heure", ascending=False).copy()
                    df_display_mgmt["Date_Str"] = df_display_mgmt["Date_Heure"].dt.strftime("%d-%m-%Y")
                    df_display_mgmt["Label"] = df_display_mgmt["Date_Str"] + " | " + df_display_mgmt["Type"] + " | " + df_display_mgmt["Nom"].fillna("")

                    options_map = {idx: f"{row['Label']}" for idx, row in df_display_mgmt.iterrows()}
                    selected_idx = st.selectbox(
                        "Sélectionner une transaction pour agir dessus :",
                        options=list(options_map.keys()),
                        format_func=lambda idx: options_map[idx],
                        index=None,
                        placeholder="Choisir..."
                    )

                    if selected_idx is not None:
                        action_choisie = st.radio("Action", ["Modifier", "Supprimer"], horizontal=True, key="act_choice_radio")
                        row_sel = df_transactions.loc[selected_idx]

                        if action_choisie == "Supprimer":
                            if st.button("🗑️ Confirmer la suppression", type="primary"):
                                df_transactions_new = df_transactions.drop(index=selected_idx).reset_index(drop=True)
                                ok_save, err_save = save_transactions_csv(df_transactions_new)
                                if ok_save:
                                    df_transactions = df_transactions_new
                                    load_data.clear()
                                    st.toast("🗑️ Transaction supprimée avec succès.", icon="✅")
                                    st.rerun()
                                else:
                                    st.error(err_save)

                        elif action_choisie == "Modifier":
                            with st.form("edit_trade_form"):
                                types_possibles = ["ACHAT", "VENTE", "APPORT", "RETRAIT", "DIVIDENDE", "SPLIT"]
                                current_type_idx = types_possibles.index(row_sel["Type"]) if row_sel["Type"] in types_possibles else 0
                                new_op_type = st.selectbox("Type d'opération", options=types_possibles, index=current_type_idx)

                                e_nom, e_ticker = row_sel["Nom"], row_sel["Ticker"]
                                e_shares, e_price, e_comm, e_ttf = 1.0, 0.0, 0.0, 0.0
                                e_montant = float(row_sel["Quantité"])
                                e_rompu = float(row_sel["Rompu"]) if pd.notnull(row_sel["Rompu"]) else 0.0
                                e_ret_etr = float(row_sel["Retenue_Source_Etrangere"]) if "Retenue_Source_Etrangere" in row_sel and pd.notnull(row_sel["Retenue_Source_Etrangere"]) else 0.0
                                e_remb_capital = float(row_sel["Remboursement_Capital"]) if "Remboursement_Capital" in row_sel and pd.notnull(row_sel["Remboursement_Capital"]) else 0.0
                                e_arrondi_courtier = float(row_sel["Arrondi_Courtier"]) if "Arrondi_Courtier" in row_sel and pd.notnull(row_sel["Arrondi_Courtier"]) else 0.0

                                if new_op_type in ["ACHAT", "VENTE"]:
                                    e_nom = st.text_input("Nom de l'action / ETF", value=row_sel["Nom"] if row_sel["Nom"] != "Compte Courant" else "")
                                    e_ticker = st.text_input("Ticker", value=row_sel["Ticker"] if row_sel["Ticker"] not in ["APPORT", "RETRAIT"] else "").upper().strip()
                                    e_shares = st.number_input("Quantité", min_value=1.0, step=1.0, value=float(row_sel["Quantité"]) if row_sel["Type"] in ["ACHAT", "VENTE"] else 1.0, format="%.0f")
                                    e_price = st.number_input("Prix unitaire (€)", min_value=0.0, step=0.0001, value=float(row_sel["Prix Unitaire (€)"]) if row_sel["Type"] in ["ACHAT", "VENTE"] else 0.0, format="%.4f")
                                    e_comm = st.number_input("Commission (€)", min_value=0.0, step=0.01, value=float(row_sel["Commission (€)"]) if row_sel["Type"] in ["ACHAT", "VENTE"] else 0.0, format="%.2f")
                                    e_ttf = st.number_input("TTF (€)", min_value=0.0, step=0.01, value=float(row_sel["TTF (€)"]) if row_sel["Type"] in ["ACHAT", "VENTE"] else 0.0, format="%.2f")

                                elif new_op_type == "APPORT":
                                    e_montant = st.number_input("Montant (€)", min_value=0.0, step=10.0, value=float(row_sel["Quantité"]) if row_sel["Type"] in ["APPORT", "RETRAIT"] else 100.0, format="%.2f")

                                elif new_op_type == "RETRAIT":
                                    e_montant = st.number_input("Montant (€)", min_value=0.0, step=10.0, value=float(row_sel["Quantité"]) if row_sel["Type"] in ["APPORT", "RETRAIT"] else 100.0, format="%.2f")

                                elif new_op_type == "DIVIDENDE":
                                    e_nom = st.text_input("Nom de l'action / ETF", value=row_sel["Nom"] if row_sel["Nom"] != "Compte Courant" else "")
                                    e_ticker = st.text_input("Ticker", value=row_sel["Ticker"] if row_sel["Ticker"] not in ["APPORT", "RETRAIT"] else "").upper().strip()
                                    e_shares = st.number_input("Quantité", min_value=0.0, step=1.0, value=float(row_sel["Quantité"]) if row_sel["Type"] == "DIVIDENDE" else 1.0, format="%.0f")
                                    e_price = st.number_input("Montant brut perçu (€)", min_value=0.0, step=0.01, value=float(row_sel["Prix Unitaire (€)"]) if row_sel["Type"] == "DIVIDENDE" else 0.0, format="%.2f")
                                    e_ret_etr = st.number_input("Retenue à la source (div) (€)", min_value=0.0, step=0.01, value=e_ret_etr, format="%.2f")
                                    e_remb_capital = st.number_input(
                                        "Remboursement de capital inclus (€) — optionnel",
                                        min_value=0.0, step=0.01, value=e_remb_capital, format="%.2f",
                                        help="À renseigner uniquement si une partie de la distribution reçue n'est pas un dividende "
                                             "mais un remboursement de capital. => Cela à pour impact la réduction du PRU de la ligne."
                                    )
                                    e_arrondi_courtier = st.number_input(
                                        "Arrondi du courtier (€) — optionnel",
                                        step=0.01, value=e_arrondi_courtier, format="%.2f",
                                        help="À renseigner lorsque le courtier applique un arrondi tel que Montant brut perçu"
                                             "soustrait de la Retenue à la source ne tombe pas exactement sur le montant net"
                                             "réellement crédité sur le compte. Indiquez ici l'écart, avec son signe, entre"
                                             "le montant net attendu (calculé) et le montant net réellement reçu que prévu à" 
                                             "été crédité : par exemple -0,01 si 0,01 € de moins"
                                    )

                                elif new_op_type == "SPLIT":
                                    e_nom = st.text_input("Nom de l'action / ETF", value=row_sel["Nom"] if row_sel["Nom"] != "Compte Courant" else "")
                                    e_ticker = st.text_input("Ticker", value=row_sel["Ticker"] if row_sel["Ticker"] not in ["APPORT", "RETRAIT"] else "").upper().strip()
                                    e_shares = st.number_input("Facteur de division ou ratio de nouvelles actions", min_value=0.0001, step=0.01, value=float(row_sel["Quantité"]) if row_sel["Type"] == "SPLIT" else 1.1, format="%.4f")
                                    e_rompu = st.number_input("Rompu versé en cash (€)", min_value=0.0, step=0.001, value=e_rompu, format="%.3f")
                                    e_date_rompus_default = row_sel["Date_Rompus"].date() if ("Date_Rompus" in row_sel and pd.notnull(row_sel["Date_Rompus"])) else row_sel["Date_Heure"].date()
                                    e_date_rompus = st.date_input(
                                        "Date de versement des rompus (si différente de la date du split)",
                                        value=e_date_rompus_default, format="DD-MM-YYYY",
                                    )

                                if new_op_type in ["APPORT", "RETRAIT", "DIVIDENDE", "SPLIT"]:
                                    e_date = st.date_input("Date", value=row_sel["Date_Heure"].date(), format="DD-MM-YYYY")
                                    e_time = time(0, 0, 0)
                                else:
                                    col_ed1, col_ed2 = st.columns(2)
                                    e_date = col_ed1.date_input("Date", value=row_sel["Date_Heure"].date(), format="DD-MM-YYYY")
                                    e_time = col_ed2.time_input("Heure", value=row_sel["Date_Heure"].time(), step=1)

                                if st.form_submit_button("✅ Valider les modifications"):
                                    try:
                                        if new_op_type == "APPORT":
                                            s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = "Compte Courant", "APPORT", e_montant, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
                                        elif new_op_type == "RETRAIT":
                                            s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = "Compte Courant", "RETRAIT", e_montant, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
                                        elif new_op_type == "SPLIT":
                                            s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = e_nom, e_ticker, e_shares, 0.0, 0.0, 0.0, e_rompu, 0.0, 0.0, 0.0
                                        elif new_op_type == "DIVIDENDE":
                                            s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = e_nom, e_ticker, e_shares, e_price, 0.0, 0.0, 0.0, e_ret_etr, e_remb_capital, e_arrondi_courtier
                                        else:
                                            s_nom, s_tick, s_qty, s_pr, s_comm, s_ttf, s_rompu, s_ret, s_remb, s_arrondi = e_nom, e_ticker, e_shares, e_price, e_comm, e_ttf, 0.0, 0.0, 0.0, 0.0

                                        frais_tot = e_comm + e_ttf + e_ret_etr if new_op_type == "DIVIDENDE" else e_comm + e_ttf

                                        df_transactions.loc[selected_idx, "Type"] = new_op_type
                                        df_transactions.loc[selected_idx, "Nom"] = s_nom
                                        df_transactions.loc[selected_idx, "Ticker"] = s_tick
                                        df_transactions.loc[selected_idx, "Quantité"] = s_qty
                                        df_transactions.loc[selected_idx, "Prix Unitaire (€)"] = s_pr
                                        df_transactions.loc[selected_idx, "Commission (€)"] = e_comm
                                        df_transactions.loc[selected_idx, "TTF (€)"] = e_ttf
                                        df_transactions.loc[selected_idx, "Frais Totaux (€)"] = frais_tot
                                        df_transactions.loc[selected_idx, "Rompu"] = s_rompu
                                        df_transactions.loc[selected_idx, "Retenue_Source_Etrangere"] = s_ret
                                        df_transactions.loc[selected_idx, "Remboursement_Capital"] = s_remb
                                        df_transactions.loc[selected_idx, "Arrondi_Courtier"] = s_arrondi
                                        df_transactions.loc[selected_idx, "Date_Heure"] = datetime.combine(e_date, e_time)
                                        df_transactions.loc[selected_idx, "Date_Rompus"] = (
                                            datetime.combine(e_date_rompus, time(0, 0, 0)) if new_op_type == "SPLIT"
                                            else datetime.combine(e_date, e_time)
                                        )

                                        ok_save, err_save = save_transactions_csv(df_transactions)
                                        if ok_save:
                                            load_data.clear()
                                            st.toast("✅ Transaction modifiée avec succès !", icon="✅")
                                            st.rerun()
                                        else:
                                            st.error(err_save)
                                    except Exception as e:
                                        st.error(f"Erreur lors de la modification : {e}")
                _gestion_transactions_fragment()

        with st.expander("🏆 Classement des actions par gain", expanded=True):
            if not df_port.empty:
                # Retour à la "Performance (%)" (à la demande) à la place du YoC, et ajout d'une
                # colonne "Nombre de mouvements" (nombre d'ACHATs + VENTEs sur la valeur) pour
                # visualiser d'un coup d'œil l'activité de chaque ligne du classement.
                df_gain_rank = df_port[['Nom', 'Capital Investi (€)', 'Gain Réalisé (€)', 'Gain Latent (€)', 'Dividendes Reçus (€)', 'Gain Total Global (€)', 'Performance (%)', 'Nb Mouvements', 'Jours Détention', 'Secondes Détention']].copy()
                df_gain_rank = df_gain_rank.rename(columns={'Nb Mouvements': 'Nombre de mouvements',
                                                            'Jours Détention': 'Détention (jour)'})

                df_gain_rank = df_gain_rank.sort_values(by='Gain Total Global (€)', ascending=False).reset_index(drop=True)
                df_gain_rank.insert(
                    df_gain_rank.columns.get_loc('Performance (%)') + 1, 'Perf. annuelle moy. (%)',
                    [_perf_annualisee(pf, j) for pf, j in zip(df_gain_rank['Performance (%)'], df_gain_rank['Détention (jour)'])]
                )
                # Contribution à la performance globale du portefeuille (en %) : gain total de la ligne ÷ total des
                # apports nets. La somme des lignes redonne la performance globale. Placée entre « Performance » et
                # « Perf. annuelle moy. ».
                df_gain_rank.insert(
                    df_gain_rank.columns.get_loc('Performance (%)') + 1, 'Contribution perf. (%)',
                    (pd.to_numeric(df_gain_rank['Gain Total Global (€)'], errors="coerce") / base_perf_globale * 100.0)
                    if base_perf_globale > 0 else np.nan
                )
                df_gain_rank.insert(0, "N°", range(1, len(df_gain_rank) + 1))

                df_gain_rank_fmt = df_gain_rank.drop(columns=['Capital Investi (€)', 'Secondes Détention']).copy()
                # Même présentation que « Détail des Positions Actives » : chiffres colorés (▲ vert / ▼ rouge) sur
                # les gains et la performance, dividendes en simple montant, une ligne grise sur deux (CSS du
                # tableau) ; plus aucun dégradé de couleur sur le nom de l'action (gris uniquement).
                for col in ['Gain Réalisé (€)', 'Gain Latent (€)', 'Gain Total Global (€)']:
                    df_gain_rank_fmt[col] = df_gain_rank_fmt[col].apply(fmt_eur_arrow)
                df_gain_rank_fmt['Dividendes Reçus (€)'] = df_gain_rank_fmt['Dividendes Reçus (€)'].apply(fmt_eur)
                df_gain_rank_fmt['Performance (%)'] = df_gain_rank_fmt['Performance (%)'].apply(lambda x: fmt_perf_simple(x))
                df_gain_rank_fmt['Perf. annuelle moy. (%)'] = df_gain_rank_fmt['Perf. annuelle moy. (%)'].apply(fmt_perf_simple)
                df_gain_rank_fmt['Contribution perf. (%)'] = df_gain_rank_fmt['Contribution perf. (%)'].apply(fmt_perf_simple)
                df_gain_rank_fmt['Détention (jour)'] = [
                    _fmt_duree_detention(j, sec)
                    for j, sec in zip(df_gain_rank['Détention (jour)'], df_gain_rank['Secondes Détention'])
                ]

                _cols_fleche_rank = ['Gain Réalisé (€)', 'Gain Latent (€)', 'Gain Total Global (€)', 'Performance (%)', 'Contribution perf. (%)', 'Perf. annuelle moy. (%)']
                # Ligne Total : somme de chaque colonne sur toutes les actions du classement. La performance n'est pas
                # totalisée ici (la base de calcul diffère selon que la position est ouverte ou soldée).
                _tot_rank = {c: "" for c in df_gain_rank_fmt.columns}
                _tot_rank["Nom"] = "Total"
                _tot_rank['Gain Réalisé (€)'] = fmt_eur_arrow(df_gain_rank['Gain Réalisé (€)'].sum())
                _tot_rank['Gain Latent (€)'] = fmt_eur_arrow(df_gain_rank['Gain Latent (€)'].sum())
                _tot_rank['Dividendes Reçus (€)'] = fmt_eur(df_gain_rank['Dividendes Reçus (€)'].sum())
                _tot_rank['Gain Total Global (€)'] = fmt_eur_arrow(df_gain_rank['Gain Total Global (€)'].sum())
                # Performance globale : gain total / base implicite de chaque ligne (gain ÷ performance).
                _pf = pd.to_numeric(df_gain_rank['Performance (%)'], errors="coerce")
                _gt = pd.to_numeric(df_gain_rank['Gain Total Global (€)'], errors="coerce")
                _ok = _pf.notna() & (_pf.abs() > 1e-9) & _gt.notna()
                _bases = (_gt[_ok] / _pf[_ok] * 100).where(lambda b: b > 0).dropna()
                if len(_bases) > 0 and _bases.sum() > 0:
                    _perf_tot = float(_gt[_bases.index].sum() / _bases.sum() * 100)
                    _jtot = float((pd.to_numeric(df_gain_rank['Détention (jour)'], errors="coerce").fillna(0)[_bases.index] * _bases).sum() / _bases.sum())
                    _tot_rank['Performance (%)'] = fmt_perf_simple(_perf_tot)
                    _tot_rank['Perf. annuelle moy. (%)'] = fmt_perf_simple(_perf_annualisee(_perf_tot, _jtot))
                if base_perf_globale > 0:
                    _tot_rank['Contribution perf. (%)'] = fmt_perf_simple(pd.to_numeric(df_gain_rank['Contribution perf. (%)'], errors="coerce").sum())
                _tot_rank['Nombre de mouvements'] = str(int(pd.to_numeric(df_gain_rank['Nombre de mouvements'], errors="coerce").fillna(0).sum()))
                _EQ_COLS_RANK = ("Gain Total Global (€)", "Performance (%)", "Contribution perf. (%)", "Perf. annuelle moy. (%)")
                _tot_rank = _dash_if_empty(pd.DataFrame([_tot_rank]), eq_cols=_EQ_COLS_RANK).iloc[0].to_dict()
                _tot_rank["N°"] = ""
                _html_table(
                    _dash_if_empty(df_gain_rank_fmt, eq_cols=_EQ_COLS_RANK),
                    cell_style=lambda c, v: _style_perf_cell(v) if c in _cols_fleche_rank else "",
                    total_row=_tot_rank,
                    max_height=386,   # 10 lignes visibles (+ ligne Total), défilement au-delà
                    sticky_col="Nom",
                )
            else:
                st.info("Aucune donnée disponible pour le classement des gains.")


# ------------------------------------------
# ONGLÊT : CLASSEMENTS
# ------------------------------------------
# ------------------------------------------
# ONGLET : APPORTS (versements)
# ------------------------------------------
if _tab_open(tab_apports):
    with tab_apports:
        PLAFOND_APPORTS = 150000.0
        _df_mv = (
            df_transactions[df_transactions["Type"].isin(["APPORT", "RETRAIT"])].copy()
            if not df_transactions.empty else pd.DataFrame()
        )
        if _df_mv.empty:
            st.info("Aucun apport enregistré pour le moment.")
        else:
            _df_mv = _df_mv.sort_values("Date_Heure")
            _df_mv["Net"] = np.where(_df_mv["Type"] == "APPORT", _df_mv["Quantité"], -_df_mv["Quantité"])
            _df_mv["Annee"] = _df_mv["Date_Heure"].dt.year
            _annees_ap = sorted(_df_mv["Annee"].unique().tolist(), reverse=True)

            # (Les filtres Année / Objectif, les indicateurs, les cartes Plafond/Objectif et la phrase
            # d'estimation ont été retirés de l'onglet : seuls les calculs servant aux graphiques restent.)
            _total_verse = float(_df_mv.loc[_df_mv["Type"] == "APPORT", "Quantité"].sum())
            _total_retire = float(_df_mv.loc[_df_mv["Type"] == "RETRAIT", "Quantité"].sum())
            _net_total = _total_verse - _total_retire

            # Série quotidienne des apports nets cumulés (base du graphique)
            _net_jour = _df_mv.groupby(_df_mv["Date_Heure"].dt.normalize())["Net"].sum().cumsum()
            _fin_serie = max(_today_paris(), _net_jour.index.max())
            _cumul = _net_jour.reindex(pd.date_range(_net_jour.index.min(), _fin_serie), method="ffill")

            with st.expander("🎯 Jauge de versements du PEA", expanded=True):
                # Le plafond de 150 000 € porte sur les versements cumulés : un retrait ne libère pas de place.
                _render_jauge_pea(_total_verse, PLAFOND_APPORTS)

            with st.expander("📈 Évolution des apports cumulés", expanded=True):
                fig_ap = go.Figure()
                fig_ap.add_trace(go.Scatter(
                    x=_cumul.index, y=_cumul.values, mode="lines", name="",
                    line=dict(color="#06b6d4", width=3, shape="hv"),
                    fill="tozeroy", fillcolor="rgba(6, 182, 212, 0.18)",
                    customdata=[fmt_eur(v) for v in _cumul.values],
                    hovertemplate="<b>%{x|%d/%m/%Y}</b><br>Apports nets cumulés : %{customdata}<extra></extra>",
                ))
                if _net_total >= 0.6 * PLAFOND_APPORTS:
                    fig_ap.add_hline(
                        y=PLAFOND_APPORTS, line_dash="dot", line_color="#d97706", line_width=1.5,
                        annotation_text="Plafond PEA", annotation_position="top left",
                        annotation_font_color="#d97706",
                    )
                fig_ap.update_layout(
                    height=340, margin=dict(l=8, r=16, t=20, b=8), hovermode="x",
                    yaxis=dict(title="", rangemode="tozero", tickformat=",.0f", ticksuffix=" €", automargin=True, nticks=6),
                    xaxis=dict(title="", tickformat="%m/%y", showgrid=False, nticks=5, automargin=True),
                )
                apply_chart_theme(fig_ap)
                _plotly_chart(fig_ap, use_container_width=True, theme=None, key="chart_apports_cumul")

            with st.expander("📊 Versements par année", expanded=True):
                _ann = sorted(_df_mv["Annee"].unique().tolist())
                _v_an = [float(_df_mv.loc[(_df_mv["Type"] == "APPORT") & (_df_mv["Annee"] == a), "Quantité"].sum()) for a in _ann]
                fig_ap_an = go.Figure()
                fig_ap_an.add_trace(go.Bar(
                    x=[str(a) for a in _ann], y=_v_an, name="Versements",
                    marker=dict(color="#06b6d4"),
                    text=[(f"{v:,.0f}".replace(",", " ") + " €") if v > 0 else "" for v in _v_an], textposition="outside", cliponaxis=False,
                    customdata=[fmt_eur(v) for v in _v_an],
                    hovertemplate="<b>%{x}</b><br>Versements : %{customdata}<extra></extra>",
                ))
                fig_ap_an.update_layout(
                    height=340, margin=dict(l=8, r=16, t=20, b=8), bargap=0.35,
                    yaxis=dict(title="", rangemode="tozero", zeroline=True, zerolinewidth=2, tickformat=",.0f", ticksuffix=" €", automargin=True, nticks=6),
                    xaxis=dict(title="", type="category", automargin=True),
                    showlegend=False,
                )
                apply_chart_theme(fig_ap_an)
                _plotly_chart(fig_ap_an, use_container_width=True, theme=None, key="chart_apports_annuels")

            _df_app_only = _df_mv[_df_mv["Type"] == "APPORT"]
            if not _df_app_only.empty:
                with st.expander("🗓️ Cartographie mensuelle des versements", expanded=True):
                    build_calendar_heatmap(
                        _df_app_only, "Date_Heure", "Quantité",
                        ["#ecfeff", "#0891b2"], "apports",
                        date_ouverture=pea_opening_dt,
                    )

            # Retraits : même présentation que les versements (graphique par année, puis cartographie mensuelle).
            _df_ret_only = _df_mv[_df_mv["Type"] == "RETRAIT"]
            if not _df_ret_only.empty:
                with st.expander("📊 Retraits par année", expanded=True):
                    _r_an = [float(_df_mv.loc[(_df_mv["Type"] == "RETRAIT") & (_df_mv["Annee"] == a), "Quantité"].sum()) for a in _ann]
                    fig_ret_an = go.Figure()
                    fig_ret_an.add_trace(go.Bar(
                        x=[str(a) for a in _ann], y=_r_an, name="Retraits",
                        marker=dict(color="#f87171"),
                        text=[(f"{v:,.0f}".replace(",", " ") + " €") if v > 0 else "" for v in _r_an], textposition="outside", cliponaxis=False,
                        customdata=[fmt_eur(v) for v in _r_an],
                        hovertemplate="<b>%{x}</b><br>Retraits : %{customdata}<extra></extra>",
                    ))
                    fig_ret_an.update_layout(
                        height=340, margin=dict(l=8, r=16, t=20, b=8), bargap=0.35,
                        yaxis=dict(title="", rangemode="tozero", zeroline=True, zerolinewidth=2, tickformat=",.0f", ticksuffix=" €", automargin=True, nticks=6),
                        xaxis=dict(title="", type="category", automargin=True),
                        showlegend=False,
                    )
                    apply_chart_theme(fig_ret_an)
                    _plotly_chart(fig_ret_an, use_container_width=True, theme=None, key="chart_retraits_annuels")

                with st.expander("🗓️ Cartographie mensuelle des retraits", expanded=True):
                    build_calendar_heatmap(
                        _df_ret_only, "Date_Heure", "Quantité",
                        ["#fef2f2", "#dc2626"], "retraits",
                        date_ouverture=pea_opening_dt,
                    )

if _tab_open(tab_classements):
    with tab_classements:
        # Filtre de période commun à tout l'onglet Classements (ventes réalisées, journées, mois,
        # années) : appliqué APRÈS les calculs de P&L et d'historique (qui ont besoin de tout
        # l'historique pour rester exacts — PRU, cumuls...), en ne gardant que les lignes dont la
        # date tombe dans la période choisie. "Tout l'historique" ne filtre rien.
        _periode_classement_choisie = st.selectbox(
            "Période du classement", _PERIODES_PRESETS, index=len(_PERIODES_PRESETS) - 1,
            key="k_periode_classements",
            help="S'applique à tous les classements de cet onglet. La journée en cours est incluse (cours en direct).",
        )
        @_cache_render
        def _rendu_onglet_classements(df_transactions, periode_classement, jour, market_epoch):
            _periode_classement_choisie = periode_classement
            _cutoff_classement = periode_debut(_periode_classement_choisie)

            # ---------------------------------------------------------------------------
            # Helpers communs aux classements "période" (journées / mois / années) : la
            # provenance du gain/perte (Vente / Achat / Dividende / Rompu), calculée une
            # seule fois pour tout l'historique, un formatage coloré vert/rouge pour le
            # survol, et un rendu de graphique générique réutilisé pour les 3 granularités.
            # ---------------------------------------------------------------------------
            def _pct_str_jour(pct):
                if pd.isna(pct):
                    return "N/A"
                return f"{pct:+.2f} %".replace(".", ",")

            # Date du tout premier ACHAT (hors apport/retrait) : sert de point de départ à tous les
            # classements de performance ci-dessous. Avant cette date, le portefeuille n'est composé que
            # de liquidités en attente d'être investies — comparer un jour "100 % cash" au jour suivant
            # (celui du premier achat) n'a pas de sens en termes de performance de marché : le calcul
            # produirait un pourcentage complètement artificiel (division par une base quasi nulle ou
            # purement en cash) et pourrait même, en % comme en €, faire ressortir un "pire jour" ou une
            # "pire année" qui ne reflète en réalité qu'un changement de composition du portefeuille (du
            # cash vers des actions) et non un vrai mouvement de marché.
            _dates_achat_seul = df_transactions.loc[df_transactions["Type"] == "ACHAT", "Date_Heure"].dropna()
            date_premier_achat = _dates_achat_seul.min().normalize() if not _dates_achat_seul.empty else None

            df_ventes_pnl_jours = compute_realized_pnl_par_vente(df_transactions) if not df_transactions.empty else pd.DataFrame()
            vente_par_jour = (
                df_ventes_pnl_jours.groupby(df_ventes_pnl_jours["Date_Heure"].dt.normalize())["Gain Réalisé (€)"].sum()
                if not df_ventes_pnl_jours.empty else pd.Series(dtype=float)
            )

            df_achats_jours = df_transactions[df_transactions["Type"] == "ACHAT"]
            achat_par_jour = (
                (-df_achats_jours["Frais Totaux (€)"]).groupby(df_achats_jours["Date_Heure"].dt.normalize()).sum()
                if not df_achats_jours.empty else pd.Series(dtype=float)
            )

            df_divs_jours = df_transactions[df_transactions["Type"] == "DIVIDENDE"].copy()
            if not df_divs_jours.empty:
                df_divs_jours["_net"] = (
                    df_divs_jours["Prix Unitaire (€)"] - df_divs_jours["Commission (€)"].fillna(0)
                    - df_divs_jours["Retenue_Source_Etrangere"].fillna(0) + df_divs_jours["Remboursement_Capital"].fillna(0)
                    + df_divs_jours.get("Arrondi_Courtier", pd.Series(0.0, index=df_divs_jours.index)).fillna(0)
                )
                div_par_jour = df_divs_jours.groupby(df_divs_jours["Date_Heure"].dt.normalize())["_net"].sum()
            else:
                div_par_jour = pd.Series(dtype=float)

            df_splits_jours = df_transactions[(df_transactions["Type"] == "SPLIT") & (df_transactions["Rompu"] > 0)].copy()
            if not df_splits_jours.empty:
                _date_eff_splits = df_splits_jours["Date_Rompus"].fillna(df_splits_jours["Date_Heure"]) if "Date_Rompus" in df_splits_jours.columns else df_splits_jours["Date_Heure"]
                rompu_par_jour = df_splits_jours.groupby(_date_eff_splits.dt.normalize())["Rompu"].sum()
            else:
                rompu_par_jour = pd.Series(dtype=float)

            def _mont_couleur(label, v):
                # Montant de la provenance en vert s'il est positif, en rouge s'il est négatif — pour
                # voir le sens de chaque ligne d'un coup d'œil au survol. Le fond de l'info-bulle étant
                # sombre (cf. hoverlabel dans apply_chart_theme), on utilise des teintes de vert/rouge
                # plus claires et lumineuses que celles utilisées ailleurs sur fond clair, afin de rester
                # lisibles sans avoir à pousser la luminosité de l'écran.
                c = "#4ade80" if v >= 0 else "#f87171"
                return f"{label} : <span style='color:{c};'>{fmt_eur(v)}</span>"

            def _breakdown_periode(date_debut, date_fin, pnl_total, label_variation="Variation"):
                mask_v = (vente_par_jour.index >= date_debut) & (vente_par_jour.index <= date_fin)
                mask_a = (achat_par_jour.index >= date_debut) & (achat_par_jour.index <= date_fin)
                mask_d = (div_par_jour.index >= date_debut) & (div_par_jour.index <= date_fin)
                mask_r = (rompu_par_jour.index >= date_debut) & (rompu_par_jour.index <= date_fin)
                v_vente = vente_par_jour[mask_v].sum() if not vente_par_jour.empty else 0.0
                v_achat = achat_par_jour[mask_a].sum() if not achat_par_jour.empty else 0.0
                v_div = div_par_jour[mask_d].sum() if not div_par_jour.empty else 0.0
                v_rompu = rompu_par_jour[mask_r].sum() if not rompu_par_jour.empty else 0.0
                v_variation = pnl_total - v_vente - v_achat - v_div - v_rompu
                lignes = [_mont_couleur(label_variation, v_variation)]
                # Ligne "Vente" affichée uniquement s'il y a effectivement eu une vente ce jour/mois/
                # année (v_vente), et seulement avec le montant de cette vente : les frais d'un simple
                # achat (v_achat) ne sont pas des plus-values/moins-values et ne doivent pas être
                # affichés sous ce libellé — ils restent inclus dans la ligne "Variation" ci-dessus.
                if abs(v_vente) > 0.005:
                    lignes.append(_mont_couleur("Vente", v_vente))
                if abs(v_div) > 0.005:
                    lignes.append(_mont_couleur("Dividende", v_div))
                if abs(v_rompu) > 0.005:
                    lignes.append(_mont_couleur("Rompu", v_rompu))
                return "<br>".join(lignes)

            def _render_period_ranking(df_subset, value_col, pnl_col, color, axis_title, is_pct, key_suffix, label_func, period_start_func, label_variation="Variation"):
                """Rendu générique réutilisé pour les journées, les mois et les années : seule change la
        colonne triée/affichée sur la barre (montant € ou impact %) ; le survol montre toujours
        l'autre unité en complément, suivi du détail de la provenance du gain/de la perte."""
                # Seules les vraies périodes gagnantes (vert) / perdantes (rouge) sont affichées : plus de lignes
                # vides sur l'axe quand il y a peu de jours / mois / trimestres / années.
                df_subset = df_subset[df_subset[value_col] > 0] if color == "#16a34a" else df_subset[df_subset[value_col] < 0]
                if df_subset.empty:
                    st.caption("Rien à afficher pour le moment.")
                    return
                _df_disp = df_subset.reset_index(drop=True)
                _labels = [label_func(d) for d in _df_disp["Date"]]
                _vals = _df_disp[value_col].tolist()
                _n = len(_df_disp)
                _y = list(range(_n - 1, -1, -1))
                _montants_fmt = [(_pct_str_jour(v) if is_pct else fmt_eur(v)) for v in _vals]
                _customdata = []
                for i in range(_n):
                    _d = _df_disp["Date"].iloc[i]
                    _pnl_total = _df_disp[pnl_col].iloc[i]
                    _pct_total = _df_disp["Impact_Pct"].iloc[i]
                    _ligne_secondaire = (
                        f"{fmt_eur(_pnl_total)} sur le portefeuille" if is_pct
                        else f"{_pct_str_jour(_pct_total)} du portefeuille"
                    )
                    _debut = period_start_func(_d)
                    _breakdown = _breakdown_periode(_debut, _d.normalize(), _pnl_total, label_variation)
                    _customdata.append((_labels[i], _ligne_secondaire, _breakdown))
                fig = go.Figure()
                _edge = max(_vals) if color == "#16a34a" else min(_vals)
                if _edge == 0:
                    _edge = 1 if color == "#16a34a" else -1
                _hover_tpl_rank = "<b>%{customdata[0]}</b><br>%{customdata[1]}<br>%{customdata[2]}<extra></extra>"
                fig.add_trace(_hover_zone_trace(_edge * 1.25, _y, _customdata, _hover_tpl_rank))
                fig.add_trace(go.Bar(
                    x=_vals, y=_y, orientation="h",
                    marker=dict(color=color),
                    customdata=_customdata,
                    text=_montants_fmt,
                    textposition="outside",
                    textfont=dict(size=11, color=color),
                    cliponaxis=False,
                    hovertemplate=_hover_tpl_rank,
                    showlegend=False,
                ))
                fig.update_layout(
                    height=max(220, 34 * _n + 40),
                    margin=dict(l=14, r=56, t=6, b=6),
                    barmode="overlay",
                    bargap=0.35,
                    xaxis=dict(title=None, showgrid=False, zeroline=True, range=[0, _edge * 1.25], showticklabels=False),
                    yaxis=dict(title=None, tickmode="array", tickvals=_y, ticktext=_labels, range=[-0.6, _n - 0.4], tickfont=dict(size=11)),
                )
                apply_chart_theme(fig)
                _plotly_chart(fig, use_container_width=True, key=f"chart_top10_{key_suffix}")

            def _build_period_rank(freq):
                """Classement générique par période (mois 'ME' ou année 'YE') : même principe que le
        classement par jour (variation de la valeur totale du portefeuille, nette des
        apports/retraits sur la période), mais construit à partir de l'historique quotidien
        rééchantillonné à la fin de chaque période."""
                _hist = get_portfolio_history(df_transactions)
                if _hist is None or _hist.empty:
                    return pd.DataFrame()
                # On ignore toute la période antérieure au premier achat (portefeuille 100 % cash) : voir
                # le commentaire sur date_premier_achat plus haut.
                if date_premier_achat is not None:
                    _hist = _hist[_hist.index >= date_premier_achat]
                if _hist.empty:
                    return pd.DataFrame()
                dfp = _hist.resample(freq).last()
                # Pour la toute première période (ex : l'année ou le mois d'ouverture du PEA, même
                # incomplète), il n'y a pas de période précédente dans l'historique tronqué : on prend
                # comme référence la valeur du portefeuille au moment exact du premier achat (= quasi
                # exclusivement du cash à cet instant, donc une base fiable et non nulle), plutôt qu'une
                # valeur avant achat ou une base à 0 qui rendrait le % incalculable. Le calcul du retour
                # de cette première période part donc bien "à partir du moment où la première action a
                # été achetée", comme pour les autres périodes.
                dfp["Valeur_Prec"] = dfp["Valeur du Portefeuille (€)"].shift(1)
                dfp["Apports_Prec"] = dfp["Apports Cumulés (€)"].shift(1)
                if len(dfp) > 0:
                    _col_vp = dfp.columns.get_loc("Valeur_Prec")
                    _col_ap = dfp.columns.get_loc("Apports_Prec")
                    dfp.iloc[0, _col_vp] = _hist.iloc[0]["Valeur du Portefeuille (€)"]
                    dfp.iloc[0, _col_ap] = _hist.iloc[0]["Apports Cumulés (€)"]
                dfp["PnL_Periode"] = (
                    (dfp["Valeur du Portefeuille (€)"] - dfp["Valeur_Prec"])
                    - (dfp["Apports Cumulés (€)"] - dfp["Apports_Prec"])
                )
                dfp["Impact_Pct"] = np.where(
                    dfp["Valeur_Prec"] > 1.0, (dfp["PnL_Periode"] / dfp["Valeur_Prec"]) * 100, np.nan,
                )
                dfp = dfp.dropna(subset=["PnL_Periode"])
                dfp = dfp[dfp["PnL_Periode"].abs() > 0.01]
                dfp = dfp.reset_index().rename(columns={"index": "Date"})
                if _cutoff_classement is not None and not dfp.empty:
                    dfp = dfp[dfp["Date"] >= _cutoff_classement]
                return dfp

            with st.expander("🎯 Meilleures et pires ventes réalisées", expanded=True):
                df_pnl_ventes_frise = compute_realized_pnl_par_vente(df_transactions) if not df_transactions.empty else pd.DataFrame()
                if _cutoff_classement is not None and not df_pnl_ventes_frise.empty:
                    df_pnl_ventes_frise = df_pnl_ventes_frise[df_pnl_ventes_frise["Date_Heure"] >= _cutoff_classement]

                if df_pnl_ventes_frise.empty:
                    st.info("Aucune vente réalisée pour le moment — ce classement apparaîtra dès la première vente.")
                else:
                    # Remplace l'ancienne "frise" chronologique (avec un nombre de transactions à
                    # choisir manuellement) par un classement fixe Top 10 gains / Top 10 pertes en deux
                    # graphiques à barres horizontales côte à côte : plus lisible pour comparer les
                    # montants entre eux qu'une frise le long d'une ligne de temps, et plus simple à
                    # utiliser puisqu'il n'y a plus rien à régler.
                    name_map_frise = df_transactions[~df_transactions["Type"].isin(["APPORT", "RETRAIT"])].groupby("Ticker")["Nom"].last().to_dict()
                    df_pnl_ventes_frise = df_pnl_ventes_frise.copy()
                    df_pnl_ventes_frise["Nom"] = df_pnl_ventes_frise["Ticker"].map(name_map_frise).fillna(df_pnl_ventes_frise["Ticker"])
                    df_pnl_ventes_frise["Date_Str"] = df_pnl_ventes_frise["Date_Heure"].dt.strftime("%d/%m/%Y")

                    df_gains_top10 = df_pnl_ventes_frise[df_pnl_ventes_frise["Gain Réalisé (€)"] > 0].nlargest(10, "Gain Réalisé (€)").sort_values("Gain Réalisé (€)")
                    df_pertes_top10 = df_pnl_ventes_frise[df_pnl_ventes_frise["Gain Réalisé (€)"] < 0].nsmallest(10, "Gain Réalisé (€)").sort_values("Gain Réalisé (€)", ascending=False)

                    def _label_frise(row):
                        nom_l = str(row["Nom"])
                        return nom_l if len(nom_l) <= 14 else nom_l[:13] + "…"  # court : 2 graphiques côte à côte (nom complet au survol)

                    def _pct_str_frise(pct):
                        if pd.isna(pct):
                            return "N/A"
                        return f"{pct:+.2f} %".replace(".", ",")

                    def _tip_col(label, txt, v):
                        # Montant coloré (vert / rouge clair, lisible sur l'infobulle sombre), comme pour les journées.
                        c = "#4ade80" if v >= 0 else "#f87171"
                        return f"{label} : <span style='color:{c};'>{txt}</span>"

                    _HOVER_TPL_FRISE = (
                        "<b>%{customdata[0]}</b><br>%{customdata[1]}<br>"
                        "%{customdata[2]}<br>%{customdata[3]}<extra></extra>"
                    )

                    def _build_bar_trace(x_vals, y_positions, color, customdata_list, montants_fmt):
                        # Barre pleine (go.Bar) au lieu de l'ancien nuage de petits points qui simulait
                        # une tige : plus lisible, et le survol fonctionne sur toute la longueur de la
                        # barre (et non plus seulement sur les points). cliponaxis=False évite que
                        # l'étiquette de valeur, affichée juste après l'extrémité de la barre, ne soit
                        # rognée par le bord du graphique pour les barres les plus longues.
                        return go.Bar(
                            x=x_vals, y=y_positions, orientation="h",
                            marker=dict(color=color),
                            customdata=customdata_list,
                            text=montants_fmt,
                            textposition="outside",
                            textfont=dict(size=11, color=color),
                            cliponaxis=False,
                            hovertemplate=_HOVER_TPL_FRISE,
                            showlegend=False,
                        )

                    col_gains_frise, col_pertes_frise = _paired_columns("sbs_rank_col_gains_frise")

                    # Totaux sur l'ENSEMBLE des ventes réalisées (pas seulement les 10 affichées dans
                    # chaque classement ci-dessous), sous la même forme de petite carte que "Total
                    # Général perçu net" utilisée sur l'onglet Dividendes.
                    _total_plus_values_actees = df_pnl_ventes_frise[df_pnl_ventes_frise["Gain Réalisé (€)"] > 0]["Gain Réalisé (€)"].sum()
                    _total_moins_values_actees = df_pnl_ventes_frise[df_pnl_ventes_frise["Gain Réalisé (€)"] < 0]["Gain Réalisé (€)"].sum()

                    with col_gains_frise:
                        render_total_card("Total des plus-values actées", _total_plus_values_actees, "#16a34a")
                        st.markdown("**📈 Top 10 des meilleures ventes**")
                        if df_gains_top10.empty:
                            st.caption("Aucun gain réalisé pour le moment.")
                        else:
                            _grid_color_top10 = "#f1f5f9"
                            # Ordre d'affichage voulu, de haut en bas : la MEILLEURE vente tout en haut,
                            # puis en descendant vers la "pire des meilleures" (la plus petite du Top 10)
                            # tout en bas — donc simplement l'ordre décroissant du gain.
                            _df_gains_disp = df_gains_top10.sort_values("Gain Réalisé (€)", ascending=False).reset_index(drop=True)
                            _labels_gains = [_label_frise(r) for _, r in _df_gains_disp.iterrows()]
                            _vals_gains = _df_gains_disp["Gain Réalisé (€)"].tolist()
                            _n_gains = len(_df_gains_disp)
                            # Axe Y NUMÉRIQUE (positions 0..N-1), et non catégoriel basé sur le nom de
                            # l'entreprise : avec un axe catégoriel, deux ventes de la MÊME entreprise
                            # partagent la même catégorie et Plotly les fusionne sur une seule ligne. En
                            # numérotant chaque ligne individuellement (avec un simple "ticktext" pour
                            # afficher quand même le nom), on garantit une ligne par mouvement, même si
                            # plusieurs viennent de la même entreprise, et donc toujours autant de lignes
                            # que de ventes dans le classement (jusqu'à 10).
                            _y_gains = list(range(_n_gains - 1, -1, -1))  # position 0 = tout en bas
                            _montants_fmt_gains = [fmt_eur(v) for v in _vals_gains]
                            _full_names_gains = _df_gains_disp["Nom"].astype(str).tolist()
                            _customdata_gains = [
                                (lbl, date_str, _tip_col("Plus-value", montant_str, val),
                                 _tip_col("Performance", _pct_str_frise(pct_val), val if pd.isna(pct_val) else pct_val))
                                for lbl, date_str, montant_str, pct_val, val in zip(
                                    _full_names_gains, _df_gains_disp["Date_Str"], _montants_fmt_gains,
                                    _df_gains_disp["Gain Réalisé (%)"], _vals_gains
                                )
                            ]
                            fig_gains_frise = go.Figure()
                            fig_gains_frise.add_trace(_hover_zone_trace(
                                (max(_vals_gains) if _vals_gains else 0) * 1.25, _y_gains, _customdata_gains, _HOVER_TPL_FRISE
                            ))
                            fig_gains_frise.add_trace(_build_bar_trace(
                                _vals_gains, _y_gains, "#16a34a", _customdata_gains, _montants_fmt_gains
                            ))
                            # Marge à droite de l'axe (dans les unités de données, pas en pixels) pour
                            # laisser la place à la valeur affichée après l'extrémité des barres : sans
                            # cette marge, la valeur de la barre la plus longue peut se retrouver coupée
                            # par le bord du graphique.
                            _max_gains = max(_vals_gains) if _vals_gains else 0
                            fig_gains_frise.update_layout(
                                height=max(220, 34 * _n_gains + 40),
                                margin=dict(l=14, r=56, t=6, b=6),
                                barmode="overlay",
                                bargap=0.35,
                                xaxis=dict(title=None, showgrid=False, zeroline=True, range=[0, _max_gains * 1.25], showticklabels=False),
                                yaxis=dict(
                                    title=None,
                                    tickmode="array", tickvals=_y_gains, ticktext=_labels_gains,
                                    range=[-0.6, _n_gains - 0.4], tickfont=dict(size=11),
                                ),
                            )
                            apply_chart_theme(fig_gains_frise)
                            _plotly_chart(fig_gains_frise, use_container_width=True, key="chart_top10_gains")

                    with col_pertes_frise:
                        render_total_card("Total des moins-values actées", _total_moins_values_actees, "#dc2626")
                        st.markdown("**📉 Top 10 des pires ventes**")
                        if df_pertes_top10.empty:
                            st.caption("Aucune perte réalisée pour le moment.")
                        else:
                            _grid_color_top10p = "#f1f5f9"
                            # Ordre d'affichage voulu, de haut en bas : la PIRE vente (perte la plus
                            # importante) tout en haut, puis en descendant vers la "moins pire" (la plus
                            # petite perte du Top 10) tout en bas — donc l'ordre croissant du gain
                            # (le plus négatif d'abord).
                            _df_pertes_disp = df_pertes_top10.sort_values("Gain Réalisé (€)", ascending=True).reset_index(drop=True)
                            _labels_pertes = [_label_frise(r) for _, r in _df_pertes_disp.iterrows()]
                            _vals_pertes = _df_pertes_disp["Gain Réalisé (€)"].tolist()
                            _n_pertes = len(_df_pertes_disp)
                            # Même correctif que pour le Top 10 des gains : axe Y numérique (et non
                            # catégoriel sur le nom de l'entreprise) pour qu'une ligne soit toujours
                            # affichée par mouvement, même si plusieurs pertes viennent de la même
                            # entreprise (sinon Plotly les fusionnait sur une seule catégorie/ligne).
                            _y_pertes = list(range(_n_pertes - 1, -1, -1))  # position 0 = tout en bas
                            _montants_fmt_pertes = [fmt_eur(v) for v in _vals_pertes]
                            _full_names_pertes = _df_pertes_disp["Nom"].astype(str).tolist()
                            _customdata_pertes = [
                                (lbl, date_str, _tip_col("Moins-value", montant_str, val),
                                 _tip_col("Performance", _pct_str_frise(pct_val), val if pd.isna(pct_val) else pct_val))
                                for lbl, date_str, montant_str, pct_val, val in zip(
                                    _full_names_pertes, _df_pertes_disp["Date_Str"], _montants_fmt_pertes,
                                    _df_pertes_disp["Gain Réalisé (%)"], _vals_pertes
                                )
                            ]
                            fig_pertes_frise = go.Figure()
                            fig_pertes_frise.add_trace(_hover_zone_trace(
                                (min(_vals_pertes) if _vals_pertes else 0) * 1.25, _y_pertes, _customdata_pertes, _HOVER_TPL_FRISE
                            ))
                            fig_pertes_frise.add_trace(_build_bar_trace(
                                _vals_pertes, _y_pertes, "#dc2626", _customdata_pertes, _montants_fmt_pertes
                            ))
                            # Axe X : en donnant un "range" dont la borne de départ (0) est supérieure à
                            # la borne d'arrivée (négative), l'axe est inversé — 0 reste à gauche, comme
                            # pour le Top 10 des gains — sans avoir besoin de "autorange: reversed". On
                            # ajoute une marge côté négatif pour laisser la place à l'étiquette de la pire
                            # vente, qui se retrouvait auparavant coupée par le bord du graphique.
                            _min_pertes = min(_vals_pertes) if _vals_pertes else 0
                            fig_pertes_frise.update_layout(
                                height=max(220, 34 * _n_pertes + 40),
                                margin=dict(l=14, r=56, t=6, b=6),
                                barmode="overlay",
                                bargap=0.35,
                                xaxis=dict(title=None, showgrid=False, zeroline=True, range=[0, _min_pertes * 1.25], showticklabels=False),
                                yaxis=dict(
                                    title=None,
                                    tickmode="array", tickvals=_y_pertes, ticktext=_labels_pertes,
                                    range=[-0.6, _n_pertes - 0.4], tickfont=dict(size=11),
                                ),
                            )
                            apply_chart_theme(fig_pertes_frise)
                            _plotly_chart(fig_pertes_frise, use_container_width=True, key="chart_top10_pertes")

            with st.expander("🏆 Meilleures et pires journées du portefeuille", expanded=True):
                history_df_days = get_portfolio_history(df_transactions)
                # On ignore toute la période antérieure au premier achat (portefeuille 100 % cash) : voir
                # le commentaire sur date_premier_achat plus haut. En tronquant AVANT de calculer les
                # diff()/shift(1), le tout premier jour conservé (celui du premier achat) se retrouve
                # sans "veille" disponible dans la série tronquée, et est donc naturellement écarté du
                # classement au lieu de produire une variation aberrante en comparant à un jour 100 % cash.
                if history_df_days is not None and not history_df_days.empty and date_premier_achat is not None:
                    history_df_days = history_df_days[history_df_days.index >= date_premier_achat]
                if history_df_days is None or history_df_days.empty:
                    st.info("Pas encore assez d'historique pour établir ce classement.")
                else:
                    df_days_rank = history_df_days.copy()

                    # Variation quotidienne de la valeur TOTALE du portefeuille (actions + espèces),
                    # nette des apports/retraits du jour : un apport ou un retrait fait varier la valeur
                    # du portefeuille sans que ce soit un gain ou une perte, donc on le retire pour
                    # n'isoler que la vraie performance du jour (plus-values actées et latentes,
                    # dividendes et rompus perçus ce jour-là).
                    df_days_rank["Valeur_Veille"] = df_days_rank["Valeur du Portefeuille (€)"].shift(1)
                    df_days_rank["PnL_Jour"] = df_days_rank["Valeur du Portefeuille (€)"].diff() - df_days_rank["Apports Cumulés (€)"].diff()
                    df_days_rank["Impact_Pct"] = np.where(
                        df_days_rank["Valeur_Veille"] > 1.0,
                        (df_days_rank["PnL_Jour"] / df_days_rank["Valeur_Veille"]) * 100,
                        np.nan,
                    )
                    df_days_rank = df_days_rank.dropna(subset=["PnL_Jour", "Impact_Pct"])
                    # On ignore les journées sans aucun mouvement de valeur (week-ends, jours fériés, ou
                    # simplement aucune séance) : sans ce filtre, elles pourraient noyer le classement si
                    # le portefeuille est encore jeune et compte moins de 10 vraies journées de variation.
                    df_days_rank = df_days_rank[df_days_rank["PnL_Jour"].abs() > 0.01]
                    df_days_rank = df_days_rank.reset_index().rename(columns={"index": "Date"})
                    if _cutoff_classement is not None and not df_days_rank.empty:
                        df_days_rank = df_days_rank[df_days_rank["Date"] >= _cutoff_classement]

                    if df_days_rank.empty:
                        st.info("Pas encore assez d'historique pour établir ce classement.")
                    else:
 
                        def _label_jour(d):
                            return d.strftime("%d/%m/%Y")

                        def _render_days_ranking(df_subset, value_col, color, axis_title, is_pct, key_suffix):
                            _render_period_ranking(
                                df_subset, value_col, "PnL_Jour", color, axis_title, is_pct,
                                f"days_{key_suffix}", _label_jour, lambda d: d.normalize(),
                                label_variation="Variation quotidienne",
                            )

                        st.markdown("#### Meilleures et pires journées du portefeuille (en €)")
                        df_best_days_eur = df_days_rank.nlargest(10, "PnL_Jour").sort_values("PnL_Jour", ascending=False)
                        df_worst_days_eur = df_days_rank.nsmallest(10, "PnL_Jour").sort_values("PnL_Jour", ascending=True)
                        col_best_eur, col_worst_eur = _paired_columns("sbs_rank_col_best_eur")
                        with col_best_eur:
                            st.markdown("**📈 Top 10 des meilleures journées**")
                            _render_days_ranking(df_best_days_eur, "PnL_Jour", "#16a34a", "Gain (€)", False, "best_eur")
                        with col_worst_eur:
                            st.markdown("**📉 Top 10 des pires journées**")
                            _render_days_ranking(df_worst_days_eur, "PnL_Jour", "#dc2626", "Perte (€)", False, "worst_eur")

                        st.markdown("<hr style='margin: 18px 0;'>", unsafe_allow_html=True)

                        st.markdown("#### Meilleures et pires journées du portefeuille (en %)")
                        df_best_days_pct = df_days_rank.nlargest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=False)
                        df_worst_days_pct = df_days_rank.nsmallest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=True)
                        col_best_pct, col_worst_pct = _paired_columns("sbs_rank_col_best_pct")
                        with col_best_pct:
                            st.markdown("**📈 Top 10 des meilleures journées**")
                            _render_days_ranking(df_best_days_pct, "Impact_Pct", "#16a34a", "Impact (%)", True, "best_pct")
                        with col_worst_pct:
                            st.markdown("**📉 Top 10 des pires journées**")
                            _render_days_ranking(df_worst_days_pct, "Impact_Pct", "#dc2626", "Impact (%)", True, "worst_pct")

            with st.expander("🏆 Meilleures et pires mois du portefeuille", expanded=True):
                df_months_rank = _build_period_rank('ME')
                if df_months_rank.empty:
                    st.info("Pas encore assez d'historique pour établir ce classement.")
                else:
                    def _label_mois(d):
                        return mois_fr(d, with_year=True)

                    def _debut_mois(d):
                        return pd.Timestamp(d.year, d.month, 1)

                    def _render_months_ranking(df_subset, value_col, color, axis_title, is_pct, key_suffix):
                        _render_period_ranking(
                            df_subset, value_col, "PnL_Periode", color, axis_title, is_pct,
                            f"months_{key_suffix}", _label_mois, _debut_mois,
                            label_variation="Variation sur le mois",
                        )

                    st.markdown("#### Meilleures et pires mois du portefeuille (en €)")
                    df_best_months_eur = df_months_rank.nlargest(10, "PnL_Periode").sort_values("PnL_Periode", ascending=False)
                    df_worst_months_eur = df_months_rank.nsmallest(10, "PnL_Periode").sort_values("PnL_Periode", ascending=True)
                    col_best_m_eur, col_worst_m_eur = _paired_columns("sbs_rank_col_best_m_eur")
                    with col_best_m_eur:
                        st.markdown("**📈 Top 10 des meilleurs mois**")
                        _render_months_ranking(df_best_months_eur, "PnL_Periode", "#16a34a", "Gain (€)", False, "best_eur")
                    with col_worst_m_eur:
                        st.markdown("**📉 Top 10 des pires mois**")
                        _render_months_ranking(df_worst_months_eur, "PnL_Periode", "#dc2626", "Perte (€)", False, "worst_eur")

                    st.markdown("<hr style='margin: 18px 0;'>", unsafe_allow_html=True)

                    st.markdown("#### Meilleures et pires mois du portefeuille (en %)")
                    df_best_months_pct = df_months_rank.nlargest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=False)
                    df_worst_months_pct = df_months_rank.nsmallest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=True)
                    col_best_m_pct, col_worst_m_pct = _paired_columns("sbs_rank_col_best_m_pct")
                    with col_best_m_pct:
                        st.markdown("**📈 Top 10 des meilleurs mois**")
                        _render_months_ranking(df_best_months_pct, "Impact_Pct", "#16a34a", "Impact (%)", True, "best_pct")
                    with col_worst_m_pct:
                        st.markdown("**📉 Top 10 des pires mois**")
                        _render_months_ranking(df_worst_months_pct, "Impact_Pct", "#dc2626", "Impact (%)", True, "worst_pct")

            with st.expander("🏆 Meilleurs et pires trimestres du portefeuille", expanded=True):
                df_quarters_rank = _build_period_rank('QE')
                if df_quarters_rank.empty:
                    st.info("Pas encore assez d'historique pour établir ce classement.")
                else:
                    def _label_trim(d):
                        return f"T{(d.month - 1) // 3 + 1} {d.year}"

                    def _debut_trim(d):
                        return pd.Timestamp(d.year, 3 * ((d.month - 1) // 3) + 1, 1)

                    def _render_quarters_ranking(df_subset, value_col, color, axis_title, is_pct, key_suffix):
                        _render_period_ranking(
                            df_subset, value_col, "PnL_Periode", color, axis_title, is_pct,
                            f"quarters_{key_suffix}", _label_trim, _debut_trim,
                            label_variation="Variation sur le trimestre",
                        )

                    st.markdown("#### Meilleurs et pires trimestres du portefeuille (en €)")
                    df_best_q_eur = df_quarters_rank.nlargest(10, "PnL_Periode").sort_values("PnL_Periode", ascending=False)
                    df_worst_q_eur = df_quarters_rank.nsmallest(10, "PnL_Periode").sort_values("PnL_Periode", ascending=True)
                    col_best_q_eur, col_worst_q_eur = _paired_columns("sbs_rank_col_best_q_eur")
                    with col_best_q_eur:
                        st.markdown("**📈 Top 10 des meilleurs trimestres**")
                        _render_quarters_ranking(df_best_q_eur, "PnL_Periode", "#16a34a", "Gain (€)", False, "best_eur")
                    with col_worst_q_eur:
                        st.markdown("**📉 Top 10 des pires trimestres**")
                        _render_quarters_ranking(df_worst_q_eur, "PnL_Periode", "#dc2626", "Perte (€)", False, "worst_eur")

                    st.markdown("<hr style='margin: 18px 0;'>", unsafe_allow_html=True)

                    st.markdown("#### Meilleurs et pires trimestres du portefeuille (en %)")
                    df_best_q_pct = df_quarters_rank.nlargest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=False)
                    df_worst_q_pct = df_quarters_rank.nsmallest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=True)
                    col_best_q_pct, col_worst_q_pct = _paired_columns("sbs_rank_col_best_q_pct")
                    with col_best_q_pct:
                        st.markdown("**📈 Top 10 des meilleurs trimestres**")
                        _render_quarters_ranking(df_best_q_pct, "Impact_Pct", "#16a34a", "Impact (%)", True, "best_pct")
                    with col_worst_q_pct:
                        st.markdown("**📉 Top 10 des pires trimestres**")
                        _render_quarters_ranking(df_worst_q_pct, "Impact_Pct", "#dc2626", "Impact (%)", True, "worst_pct")

            with st.expander("🏆 Meilleures et pires années du portefeuille", expanded=True):
                df_years_rank = _build_period_rank('YE')
                if df_years_rank.empty:
                    st.info("Pas encore assez d'historique pour établir ce classement.")
                else:
                    def _label_annee(d):
                        return str(d.year)

                    def _debut_annee(d):
                        return pd.Timestamp(d.year, 1, 1)

                    def _render_years_ranking(df_subset, value_col, color, axis_title, is_pct, key_suffix):
                        _render_period_ranking(
                            df_subset, value_col, "PnL_Periode", color, axis_title, is_pct,
                            f"years_{key_suffix}", _label_annee, _debut_annee,
                            label_variation="Variation sur l'année",
                        )

                    st.markdown("#### Meilleures et pires années du portefeuille (en €)")
                    df_best_years_eur = df_years_rank.nlargest(10, "PnL_Periode").sort_values("PnL_Periode", ascending=False)
                    df_worst_years_eur = df_years_rank.nsmallest(10, "PnL_Periode").sort_values("PnL_Periode", ascending=True)
                    col_best_y_eur, col_worst_y_eur = _paired_columns("sbs_rank_col_best_y_eur")
                    with col_best_y_eur:
                        st.markdown("**📈 Meilleures années**")
                        _render_years_ranking(df_best_years_eur, "PnL_Periode", "#16a34a", "Gain (€)", False, "best_eur")
                    with col_worst_y_eur:
                        st.markdown("**📉 Pires années**")
                        _render_years_ranking(df_worst_years_eur, "PnL_Periode", "#dc2626", "Perte (€)", False, "worst_eur")

                    st.markdown("<hr style='margin: 18px 0;'>", unsafe_allow_html=True)

                    st.markdown("#### Meilleures et pires années du portefeuille (en %)")
                    df_best_years_pct = df_years_rank.nlargest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=False)
                    df_worst_years_pct = df_years_rank.nsmallest(10, "Impact_Pct").sort_values("Impact_Pct", ascending=True)
                    col_best_y_pct, col_worst_y_pct = _paired_columns("sbs_rank_col_best_y_pct")
                    with col_best_y_pct:
                        st.markdown("**📈 Meilleures années**")
                        _render_years_ranking(df_best_years_pct, "Impact_Pct", "#16a34a", "Impact (%)", True, "best_pct")
                    with col_worst_y_pct:
                        st.markdown("**📉 Pires années**")
                        _render_years_ranking(df_worst_years_pct, "Impact_Pct", "#dc2626", "Impact (%)", True, "worst_pct")
        _rendu_onglet_classements(df_transactions, _periode_classement_choisie, _now_paris().strftime("%Y-%m-%d"), _epoch_now)


# ------------------------------------------
# ONGLÊT : SAISONNALITÉ DES PLUS-VALUES ACTÉES
# ------------------------------------------
if _tab_open(tab_saisonnalite):
    with tab_saisonnalite:
        @_cache_render
        def _rendu_onglet_saisonnalite(df_transactions, jour, market_epoch):
            with st.expander("🗓️ Plus-Values Actées par Trimestre", expanded=True):
                df_ventes_pnl_trim = compute_realized_pnl_par_vente(df_transactions)

                if not df_ventes_pnl_trim.empty:
                    df_ventes_pnl_trim = df_ventes_pnl_trim.copy()
                    df_ventes_pnl_trim["_trim"] = (df_ventes_pnl_trim["Date_Heure"].dt.month - 1) // 3 + 1

                    labels_trim = ["T1 (Jan–Mar)", "T2 (Avr–Juin)", "T3 (Juil–Sep)", "T4 (Oct–Déc)"]
                    gains_par_trim = df_ventes_pnl_trim.groupby("_trim")["Gain Réalisé (€)"].sum()
                    nb_par_trim = df_ventes_pnl_trim.groupby("_trim").size()

                    valeurs_trim = [float(gains_par_trim.get(i + 1, 0.0)) for i in range(4)]
                    comptes_trim = [int(nb_par_trim.get(i + 1, 0)) for i in range(4)]
                    couleurs_barres_trim = ["#0d9488" if v >= 0 else "#ef4444" for v in valeurs_trim]
                    couleurs_bordure_trim = ["#0f766e" if v >= 0 else "#dc2626" for v in valeurs_trim]

                    y_max_trim = max(valeurs_trim)
                    y_min_trim = min(valeurs_trim)
                    spread_trim = (y_max_trim - y_min_trim) if y_max_trim != y_min_trim else max(abs(y_max_trim), 1.0)
                    pad_trim = spread_trim * 0.18
                    range_top_trim = (y_max_trim + pad_trim) if y_max_trim > 0 else pad_trim * 0.4
                    range_bottom_trim = (y_min_trim - pad_trim) if y_min_trim < 0 else -pad_trim * 0.4

                    _montants_html_trim = [
                        f"<span style='color:{'#16a34a' if v >= 0 else '#dc2626'};'><b>{fmt_eur(v)}</b></span>"
                        for v in valeurs_trim
                    ]
                    fig_trim = go.Figure(data=go.Bar(
                        x=labels_trim,
                        y=valeurs_trim,
                        marker=dict(color=couleurs_barres_trim, line=dict(color=couleurs_bordure_trim, width=1)),
                        customdata=list(zip(_montants_html_trim, comptes_trim)),
                        hovertemplate="%{customdata[0]}<br>%{customdata[1]} vente(s) actée(s)<extra></extra>",
                    ))
                    fig_trim.update_layout(
                        height=380,
                        margin=dict(l=10, r=10, t=20, b=10),
                        bargap=0.3,
                        hovermode="x",
                        yaxis=dict(
                            title="Plus-value actée (€)", zeroline=True, zerolinewidth=2,
                            range=[range_bottom_trim, range_top_trim],
                        ),
                        xaxis=dict(
                            title="", showticklabels=True, tickmode="array",
                            tickvals=labels_trim, ticktext=labels_trim,
                            tickfont=dict(size=10, color="#475569"),
                            showline=False, ticks="",
                            showgrid=True, gridcolor="#e2e8f0", griddash="dot",
                        ),
                    )
                    apply_chart_theme(fig_trim)
                    _plotly_chart(fig_trim, use_container_width=True, key="gain_trimestre_chart")
                else:
                    st.info("Aucune vente enregistrée pour le moment.")

            with st.expander("🗓️ Plus-Values Actées par Mois de l'Année", expanded=True):
                df_ventes_pnl_mois = compute_realized_pnl_par_vente(df_transactions)

                if not df_ventes_pnl_mois.empty:
                    df_ventes_pnl_mois = df_ventes_pnl_mois.copy()
                    df_ventes_pnl_mois["_mois"] = df_ventes_pnl_mois["Date_Heure"].dt.month

                    labels_mois = [
                        "Janvier", "Février", "Mars", "Avril", "Mai", "Juin",
                        "Juillet", "Août", "Septembre", "Octobre", "Novembre", "Décembre"
                    ]
                    nb_mois = 12

                    gains_par_mois = df_ventes_pnl_mois.groupby("_mois")["Gain Réalisé (€)"].sum()
                    nb_par_mois = df_ventes_pnl_mois.groupby("_mois").size()

                    valeurs_mois = [float(gains_par_mois.get(i + 1, 0.0)) for i in range(nb_mois)]
                    comptes_mois = [int(nb_par_mois.get(i + 1, 0)) for i in range(nb_mois)]
                    couleurs_barres_mois = ["#0d9488" if v >= 0 else "#ef4444" for v in valeurs_mois]
                    couleurs_bordure_mois = ["#0f766e" if v >= 0 else "#dc2626" for v in valeurs_mois]

                    y_max_mois = max(valeurs_mois) if valeurs_mois else 0.0
                    y_min_mois = min(valeurs_mois) if valeurs_mois else 0.0
                    spread_mois = (y_max_mois - y_min_mois) if y_max_mois != y_min_mois else max(abs(y_max_mois), 1.0)
                    pad_mois = spread_mois * 0.18
                    range_top_mois = (y_max_mois + pad_mois) if y_max_mois > 0 else pad_mois * 0.4
                    range_bottom_mois = (y_min_mois - pad_mois) if y_min_mois < 0 else -pad_mois * 0.4

                    # Montant coloré en vert (positif) ou rouge (négatif) dans l'info-bulle, comme
                    # demandé, pour repérer le sens du mois d'un coup d'œil sans lire le signe.
                    _montants_html_mois = [
                        f"<span style='color:{'#16a34a' if v >= 0 else '#dc2626'};'><b>{fmt_eur(v)}</b></span>"
                        for v in valeurs_mois
                    ]
                    fig_mois = go.Figure(data=go.Bar(
                        x=labels_mois,
                        y=valeurs_mois,
                        marker=dict(color=couleurs_barres_mois, line=dict(color=couleurs_bordure_mois, width=1)),
                        customdata=list(zip(_montants_html_mois, comptes_mois)),
                        hovertemplate="%{customdata[0]}<br>%{customdata[1]} vente(s) actée(s)<extra></extra>",
                    ))

                    # Axe des abscisses classique, en dur sous le graphique (au lieu d'étiquettes
                    # flottantes sur la ligne du zéro) : chaque mois reste toujours visible même sur les
                    # barres minuscules, et un quadrillage vertical pointillé, clair, matérialise la
                    # frontière entre deux mois pour mieux les distinguer quand leurs plus-values sont
                    # faibles. Comme le nom du mois est maintenant affiché en permanence, il n'a plus
                    # besoin d'être répété dans l'info-bulle au survol : celle-ci ne garde que le montant
                    # et le nombre de ventes.
                    _axis_label_color_mois = "#475569"
                    _grid_color_mois = "#e2e8f0"

                    fig_mois.update_layout(
                        height=380,
                        margin=dict(l=10, r=10, t=20, b=10),
                        bargap=0.3,
                        hovermode="x",
                        yaxis=dict(
                            title="Plus-value actée (€)", zeroline=True, zerolinewidth=2,
                            range=[range_bottom_mois, range_top_mois],
                        ),
                        xaxis=dict(
                            title="", showticklabels=True, tickmode="array",
                            tickvals=labels_mois, ticktext=labels_mois,
                            tickfont=dict(size=10, color=_axis_label_color_mois),
                            showline=False, ticks="",
                            showgrid=True, gridcolor=_grid_color_mois, griddash="dot",
                        ),
                    )
                    apply_chart_theme(fig_mois)
                    _plotly_chart(fig_mois, use_container_width=True, key="gain_mois_chart")
                else:
                    st.info("Aucune vente enregistrée pour le moment.")

            with st.expander("📅 Plus-Values Actées par Jour de la Semaine", expanded=True):
                df_ventes_pnl_jour = compute_realized_pnl_par_vente(df_transactions)

                if not df_ventes_pnl_jour.empty:
                    df_ventes_pnl_jour = df_ventes_pnl_jour.copy()
                    df_ventes_pnl_jour["_weekday"] = df_ventes_pnl_jour["Date_Heure"].dt.weekday

                    labels_jours = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi"]
                    nb_jours = 5

                    mask_semaine = df_ventes_pnl_jour["_weekday"] <= 4
                    df_semaine = df_ventes_pnl_jour[mask_semaine].copy()
                    df_hors_semaine = df_ventes_pnl_jour[~mask_semaine]

                    if not df_semaine.empty:
                        gains_par_jour = df_semaine.groupby("_weekday")["Gain Réalisé (€)"].sum()
                        nb_par_jour = df_semaine.groupby("_weekday").size()
                    else:
                        gains_par_jour = pd.Series(dtype=float)
                        nb_par_jour = pd.Series(dtype=int)

                    valeurs_jours = [float(gains_par_jour.get(i, 0.0)) for i in range(nb_jours)]
                    comptes_jours = [int(nb_par_jour.get(i, 0)) for i in range(nb_jours)]
                    couleurs_barres_jours = ["#0d9488" if v >= 0 else "#ef4444" for v in valeurs_jours]
                    couleurs_bordure_jours = ["#0f766e" if v >= 0 else "#dc2626" for v in valeurs_jours]

                    y_max_jours = max(valeurs_jours) if valeurs_jours else 0.0
                    y_min_jours = min(valeurs_jours) if valeurs_jours else 0.0
                    spread_jours = (y_max_jours - y_min_jours) if y_max_jours != y_min_jours else max(abs(y_max_jours), 1.0)
                    pad_jours = spread_jours * 0.18
                    range_top_jours = (y_max_jours + pad_jours) if y_max_jours > 0 else pad_jours * 0.4
                    range_bottom_jours = (y_min_jours - pad_jours) if y_min_jours < 0 else -pad_jours * 0.4

                    _montants_html_jours = [
                        f"<span style='color:{'#16a34a' if v >= 0 else '#dc2626'};'><b>{fmt_eur(v)}</b></span>"
                        for v in valeurs_jours
                    ]
                    fig_jours = go.Figure(data=go.Bar(
                        x=labels_jours,
                        y=valeurs_jours,
                        marker=dict(color=couleurs_barres_jours, line=dict(color=couleurs_bordure_jours, width=1)),
                        customdata=list(zip(_montants_html_jours, comptes_jours)),
                        hovertemplate="%{customdata[0]}<br>%{customdata[1]} vente(s) actée(s)<extra></extra>",
                    ))

                    _axis_label_color_jours = "#475569"
                    _grid_color_jours = "#e2e8f0"

                    fig_jours.update_layout(
                        height=380,
                        margin=dict(l=10, r=10, t=20, b=10),
                        bargap=0.3,
                        hovermode="x",
                        yaxis=dict(
                            title="Plus-value actée (€)", zeroline=True, zerolinewidth=2,
                            range=[range_bottom_jours, range_top_jours],
                        ),
                        xaxis=dict(
                            title="", showticklabels=True, tickmode="array",
                            tickvals=labels_jours, ticktext=labels_jours,
                            tickfont=dict(size=10, color=_axis_label_color_jours),
                            showline=False, ticks="",
                            showgrid=True, gridcolor=_grid_color_jours, griddash="dot",
                        ),
                    )
                    apply_chart_theme(fig_jours)
                    _plotly_chart(fig_jours, use_container_width=True, key="gain_jour_semaine_chart")

                    if not df_hors_semaine.empty:
                        total_hors_semaine = df_hors_semaine["Gain Réalisé (€)"].sum()
                        st.caption(
                            f"ℹ️ {len(df_hors_semaine)} vente(s) enregistrée(s) un week-end, "
                            f"pour {fmt_eur(total_hors_semaine)}, non représentée(s) ci-dessus."
                        )
                else:
                    st.info("Aucune vente enregistrée pour le moment.")

            with st.expander("⏰ Plus-Values Actées par Tranche Horaire", expanded=True):
                df_ventes_pnl = compute_realized_pnl_par_vente(df_transactions)

                if not df_ventes_pnl.empty:
                    df_ventes_pnl = df_ventes_pnl.copy()
                    df_ventes_pnl["_minutes"] = df_ventes_pnl["Date_Heure"].apply(lambda d: d.hour * 60 + d.minute)

                    MIN_OUVERTURE, MIN_CLOTURE = 9 * 60, 17 * 60 + 30  # 9h00 -> 17h30
                    mask_seance = (df_ventes_pnl["_minutes"] >= MIN_OUVERTURE) & (df_ventes_pnl["_minutes"] < MIN_CLOTURE)
                    df_seance = df_ventes_pnl[mask_seance].copy()
                    df_hors_seance = df_ventes_pnl[~mask_seance]

                    def _fmt_hm(total_min):
                        h, m = divmod(total_min, 60)
                        return f"{h}h{m:02d}"

                    TRANCHE_MIN = 30
                    nb_tranches = (MIN_CLOTURE - MIN_OUVERTURE) // TRANCHE_MIN
                    labels_tranches = [
                        f"{_fmt_hm(MIN_OUVERTURE + i * TRANCHE_MIN)} – {_fmt_hm(MIN_OUVERTURE + (i + 1) * TRANCHE_MIN)}"
                        for i in range(nb_tranches)
                    ]

                    if not df_seance.empty:
                        df_seance["_tranche"] = ((df_seance["_minutes"] - MIN_OUVERTURE) // TRANCHE_MIN).astype(int)
                        gains_par_tranche = df_seance.groupby("_tranche")["Gain Réalisé (€)"].sum()
                        nb_par_tranche = df_seance.groupby("_tranche").size()
                    else:
                        gains_par_tranche = pd.Series(dtype=float)
                        nb_par_tranche = pd.Series(dtype=int)

                    valeurs = [float(gains_par_tranche.get(i, 0.0)) for i in range(nb_tranches)]
                    comptes = [int(nb_par_tranche.get(i, 0)) for i in range(nb_tranches)]
                    couleurs_barres = ["#0d9488" if v >= 0 else "#ef4444" for v in valeurs]
                    couleurs_bordure = ["#0f766e" if v >= 0 else "#dc2626" for v in valeurs]

                    # Affinage de l'axe Y indépendamment en positif et en négatif, à partir des valeurs
                    # réelles du graphique (plutôt que l'auto-range générique de Plotly).
                    y_max = max(valeurs) if valeurs else 0.0
                    y_min = min(valeurs) if valeurs else 0.0
                    spread = (y_max - y_min) if y_max != y_min else max(abs(y_max), 1.0)
                    pad = spread * 0.18
                    range_top = (y_max + pad) if y_max > 0 else pad * 0.4
                    range_bottom = (y_min - pad) if y_min < 0 else -pad * 0.4

                    _montants_html_horaire = [
                        f"<span style='color:{'#16a34a' if v >= 0 else '#dc2626'};'><b>{fmt_eur(v)}</b></span>"
                        for v in valeurs
                    ]
                    fig_horaire = go.Figure(data=go.Bar(
                        x=labels_tranches,
                        y=valeurs,
                        marker=dict(color=couleurs_barres, line=dict(color=couleurs_bordure, width=1)),
                        # Pas de "text" sur les barres (qui s'afficherait dessus par défaut) : le détail
                        # passe uniquement par customdata + hovertemplate, jamais visible sauf au survol.
                        customdata=list(zip(_montants_html_horaire, comptes)),
                        hovertemplate="%{customdata[0]}<br>%{customdata[1]} vente(s) actée(s)<extra></extra>",
                    ))

                    _axis_label_color = "#475569"
                    _grid_color = "#e2e8f0"

                    fig_horaire.update_layout(
                        height=380,
                        margin=dict(l=10, r=10, t=20, b=10),
                        bargap=0.3,
                        # hovermode="x" : la zone sensible au survol couvre toute la hauteur de la
                        # colonne (pas seulement les quelques pixels de la barre elle-même), ce qui
                        # permet de lire les infos même sur une vente minuscule (ex. 3 € quand l'axe
                        # va jusqu'à 500 €), en passant la souris n'importe où dans sa tranche horaire.
                        hovermode="x",
                        yaxis=dict(
                            title="Plus-value actée (€)", zeroline=True, zerolinewidth=2,
                            range=[range_bottom, range_top],
                        ),
                        xaxis=dict(
                            title="", showticklabels=True, tickmode="array",
                            tickvals=labels_tranches, ticktext=labels_tranches,
                            tickfont=dict(size=10, color=_axis_label_color),
                            showline=False, ticks="",
                            showgrid=True, gridcolor=_grid_color, griddash="dot",
                        ),
                    )
                    apply_chart_theme(fig_horaire)
                    _plotly_chart(fig_horaire, use_container_width=True, key="gain_horaire_chart")

                    if not df_hors_seance.empty:
                        total_hors_seance = df_hors_seance["Gain Réalisé (€)"].sum()
                        st.caption(
                            f"ℹ️ {len(df_hors_seance)} vente(s) enregistrée(s) avec une heure hors séance "
                            f"(avant 9h00 ou après 17h30), pour {fmt_eur(total_hors_seance)}, non représentée(s) ci-dessus."
                        )
                else:
                    st.info("Aucune vente enregistrée pour le moment.")
        _rendu_onglet_saisonnalite(df_transactions, _now_paris().strftime("%Y-%m-%d"), _epoch_now)
# ------------------------------------------
# ONGLÊT 3 : PERFORMANCES & INDICES
# ------------------------------------------
if _tab_open(tab_perf):
    with tab_perf:
        # Renseignées par le graphique ci-dessous (période choisie) et réutilisées par le tableau comparatif.
        perf_port_selection = None
        _perf_sel_idx = None
        _perf_sel_bornes = None
        with st.expander("📈 Graphique de Performance Comparée (%)", expanded=True):
            if not df_transactions.empty:
                history_data = get_portfolio_history(df_transactions)
                if history_data is not None and not history_data.empty:
                
                    if "Date" in history_data.columns:
                        history_data = history_data.sort_values(by="Date").reset_index(drop=True)
                    elif isinstance(history_data.index, pd.DatetimeIndex):
                        history_data = history_data.sort_index()

                    history_data_clean = history_data[history_data["Valeur du Portefeuille (€)"] > 0] if "Valeur du Portefeuille (€)" in history_data.columns else history_data
                
                    min_graph_date = history_data_clean.index.min().date()
                    max_graph_date = history_data_clean.index.max().date()
                
                    min_tx_date = df_transactions["Date_Heure"].dropna().min()
                    min_tx_date_val = min_tx_date.date() if pd.notnull(min_tx_date) else min_graph_date
                    pea_opening_exact_date = max(min_tx_date_val, min_graph_date)

                    # Bornes par défaut du filtre de dates : premier ACHAT du PEA (hors apport/retrait,
                    # qui ne sont pas des mouvements de marché) jusqu'à AUJOURD'HUI (et non la date du
                    # dernier mouvement) — sinon, sans transaction récente, le dernier point de la
                    # courbe "Mon Portefeuille" reste figé au prix du jour de la dernière opération
                    # alors que la métrique "Perf. Globale" de la Vue d'ensemble, elle, se recalcule
                    # en continu avec les cours du jour : c'est cet écart de date qui causait le
                    # décalage entre la performance affichée ici et celle affichée ailleurs sur le
                    # dashboard.
                    _dates_hors_apport = df_transactions.loc[
                        ~df_transactions["Type"].isin(["APPORT", "RETRAIT"]), "Date_Heure"
                    ].dropna()
                    _default_perf_date_debut = _dates_hors_apport.min().date() if not _dates_hors_apport.empty else min_graph_date
                    _default_perf_date_fin = max_graph_date
                    _default_perf_date_debut = min(max(_default_perf_date_debut, min_graph_date), max_graph_date)
                    _default_perf_date_fin = min(max(_default_perf_date_fin, min_graph_date), max_graph_date)

                    st.markdown("##### 🗓️ Période affichée")
                    # Le sélecteur sert de raccourci : il remplit les deux dates ci-dessous. Modifier une date à
                    # la main bascule automatiquement le sélecteur sur « Période personnalisée ».
                    _perf_max_picker = max(max_graph_date, _today_paris().date())

                    def _perf_dates_preset(_lbl):
                        _deb = periode_debut(_lbl)
                        _d0 = _default_perf_date_debut if _deb is None else min(max(_deb.date(), min_graph_date), max_graph_date)
                        return _d0, _default_perf_date_fin

                    def _perf_vers_perso():
                        st.session_state["k_periode_perf"] = "Période personnalisée"

                    periode_perf = st.selectbox(
                        "Période", _PERIODES_PRESETS + ["Période personnalisée"],
                        index=len(_PERIODES_PRESETS) - 1, key="k_periode_perf",
                        help="Par défaut : du premier achat du PEA jusqu'à aujourd'hui. Choisissez un raccourci ou saisissez directement les deux dates ci-dessous. La performance est recalculée à partir de 0% au début de la période, pour votre portefeuille et pour les indices comparés."
                    )
                    if periode_perf == "Période personnalisée":
                        for _k_pd, _dflt_pd in (("k_perf_graph_date_debut", _default_perf_date_debut),
                                                ("k_perf_graph_date_fin", _default_perf_date_fin)):
                            _v_pd = st.session_state.get(_k_pd, _dflt_pd)
                            if isinstance(_v_pd, datetime):
                                _v_pd = _v_pd.date()
                            if not isinstance(_v_pd, date):
                                _v_pd = _dflt_pd
                            st.session_state[_k_pd] = min(max(_v_pd, min_graph_date), _perf_max_picker)
                    else:
                        (st.session_state["k_perf_graph_date_debut"],
                         st.session_state["k_perf_graph_date_fin"]) = _perf_dates_preset(periode_perf)

                    with st.container(key="compact_cols_perf_dates"):
                        col_perf_date1, col_perf_date2 = st.columns(2)
                        with col_perf_date1:
                            graph_date_debut = st.date_input(
                                "Date de début",
                                min_value=min_graph_date,
                                max_value=_perf_max_picker,
                                format="DD-MM-YYYY",
                                key="k_perf_graph_date_debut",
                                on_change=_perf_vers_perso,
                            )
                        with col_perf_date2:
                            graph_date_fin = st.date_input(
                                "Date de fin",
                                min_value=min_graph_date,
                                max_value=_perf_max_picker,
                                format="DD-MM-YYYY",
                                key="k_perf_graph_date_fin",
                                on_change=_perf_vers_perso,
                            )
                    # Pas de données au-delà du dernier jour de l'historique.
                    graph_date_debut = min(graph_date_debut or _default_perf_date_debut, max_graph_date)
                    graph_date_fin = min(graph_date_fin or _default_perf_date_fin, max_graph_date)
                    if graph_date_debut > graph_date_fin:
                        st.warning("⚠️ La date de début est postérieure à la date de fin : les deux bornes ont été inversées.")
                        graph_date_debut, graph_date_fin = graph_date_fin, graph_date_debut
                    placeholder_resume_perf = st.empty()   # valeurs début / fin + performance (remplie plus bas)

                    dt_graph_start = pd.Timestamp(graph_date_debut)
                    dt_graph_end = pd.Timestamp(graph_date_fin)
                    sub_history_graph = history_data_clean.loc[(history_data_clean.index >= dt_graph_start) & (history_data_clean.index <= dt_graph_end)].copy()

                    if not sub_history_graph.empty:
                        base_row_idx = max(int(history_data_clean.index.get_indexer([dt_graph_start], method='pad')[0]), 0)
                        base_val = history_data_clean.iloc[base_row_idx]["Valeur du Portefeuille (€)"]
                        base_app = history_data_clean.iloc[base_row_idx]["Apports Cumulés (€)"]
                    
                        # Dénominateur : deux cas de figure bien différents.
                        # 1) Période complète (réglage par défaut : ouverture du PEA -> aujourd'hui) :
                        #    même base que la métrique "Perf. Globale" du dashboard (total des apports
                        #    net, avec les mêmes replis). Nécessaire car cette base "au début de
                        #    période" ne tient pas compte des apports arrivés EN COURS de période — or
                        #    sur toute la durée de vie du PEA, il y a presque toujours eu plusieurs
                        #    versements après le tout premier ; diviser tous les gains cumulés (y
                        #    compris ceux de l'argent versé plus tard) par la seule valeur du tout
                        #    premier versement donnait des pourcentages complètement aberrants.
                        # 2) Sous-période choisie manuellement (ex. un seul mois) : valeur du
                        #    portefeuille en DÉBUT DE CETTE SOUS-PÉRIODE (comme pour "Historique des
                        #    performances mensuelles"), qui reste fiable tant qu'il n'y a pas de gros
                        #    versement en plein milieu de la fenêtre sélectionnée — cas nettement plus
                        #    rare sur une fenêtre courte que sur la durée de vie complète du PEA.
                        _periode_complete = (graph_date_debut <= _default_perf_date_debut) and (graph_date_fin >= _default_perf_date_fin)
                        if _periode_complete:
                            base_denom = base_perf_globale if base_perf_globale > 0 else 1.0
                        else:
                            base_denom = base_val if base_val > 0 else (base_app if base_app > 0 else (base_perf_globale if base_perf_globale > 0 else 1.0))

                        # Vectorisé (calcul pandas sur les colonnes entières) plutôt qu'une boucle
                        # Python avec .iterrows() sur 1300+ lignes : .iterrows() a un coût non
                        # négligeable (reconstruction d'un objet Series à chaque ligne) même pour un
                        # calcul aussi simple qu'ici — la formule elle-même ne change pas d'une ligne
                        # à l'autre selon _periode_complete, donc pas besoin de boucler du tout.
                        _val_c_s = sub_history_graph["Valeur du Portefeuille (€)"]
                        _app_c_s = sub_history_graph["Apports Cumulés (€)"]
                        if _periode_complete:
                            # Pas de soustraction de baseline ici : la courbe suit directement
                            # (valeur - apports) / base, exactement comme la métrique "Perf. Globale"
                            # du dashboard à tout instant. Forcer le premier point de la courbe à
                            # exactement 0 % (en soustrayant la valeur de départ, comme pour une
                            # sous-période) créait un écart avec cette métrique dès qu'elle ne partait
                            # pas elle-même de 0 % au même instant.
                            sub_history_graph["Perf_Port_Pct"] = ((_val_c_s - _app_c_s) / base_denom) * 100
                        else:
                            sub_history_graph["Perf_Port_Pct"] = (((_val_c_s - _app_c_s) - (base_val - base_app)) / base_denom) * 100

                        available_indices_dict = {
                            "CAC 40": "^FCHI",
                            "MSCI World": "URTH",
                            "S&P 500": "^GSPC",
                            "Stoxx 600": "^STOXX",
                            "Nasdaq 100": "^NDX",
                            "Euro Stoxx 50": "^STOXX50E",
                            "Russell 2000": "^RUT",
                            "Emerging Markets": "EEM",
                            "Nikkei 225": "^N225"
                        }

                        available_indices_help = {
                            "CAC 40": "Indice phare de la bourse de Paris (40 plus grandes capitalisations françaises).",
                            "MSCI World": "Indice boursier mondial de référence (actions des pays développés).",
                            "S&P 500": "Indice américain regroupant les 500 plus grandes entreprises cotées aux USA.",
                            "Stoxx 600": "Indice paneuropéen représentant 600 grandes, moyennes et petites capitalisations.",
                            "Nasdaq 100": "Indice américain axé sur la technologie (100 plus grandes entreprises non financières).",
                            "Euro Stoxx 50": "Indice vedette de la zone euro (50 plus grandes entreprises de la région).",
                            "Russell 2000": "Indice américain représentant les petites capitalisations (small caps).",
                            "Emerging Markets": "Indice mesurant la performance des actions de grands marchés émergents.",
                            "Nikkei 225": "Principal indice boursier de la bourse de Tokyo (225 entreprises majeures japonaises)."
                        }
                    
                        color_palette = {
                            "Mon Portefeuille": ('#0284c7', 2.5),
                            "CAC 40": ('#e11d48', 1.5),
                            "MSCI World": ('#9333ea', 1.5),
                            "S&P 500": ('#d97706', 1.5),
                            "Stoxx 600": ('#059669', 1.5),
                            "Nasdaq 100": ('#db2777', 1.5),
                            "Euro Stoxx 50": ('#4f46e5', 1.5),
                            "Russell 2000": ('#ea580c', 1.5),
                            "Emerging Markets": ('#0891b2', 1.5),
                            "Nikkei 225": ('#ca8a04', 1.5)
                        }

                        benchmarks = {
                            "Mon Portefeuille": (sub_history_graph["Perf_Port_Pct"], color_palette["Mon Portefeuille"][0], color_palette["Mon Portefeuille"][1])
                        }

                        # Disposition : sélection des indices AU-DESSUS, graphique pleine largeur,
                        # légende EN DESSOUS, puis la description des indices.
                        st.markdown("##### ⚙️ Sélection des indices à comparer")
                        indices_options_list = list(available_indices_dict.keys())
                        selected_benchmarks = st.multiselect(
                            "Choisissez un indice à comparer",
                            options=indices_options_list,
                            default=[],
                            label_visibility="collapsed",
                            placeholder="Choisissez un ou plusieurs indices à comparer",
                            key="multiselect_indices_benchmarks",
                            help="Sélectionnez un ou plusieurs indices pour comparer la performance de votre portefeuille."
                        )
                        _perf_longue = (graph_date_fin - graph_date_debut).days > 365
                        chart_slot = st.container()          # graphique (rempli plus bas)
                        placeholder_legende = st.empty()     # légende (remplie plus bas)

                        for b_name in selected_benchmarks:
                            if b_name in available_indices_dict:
                                t_symbol = available_indices_dict[b_name]
                                col_c, col_w = color_palette.get(b_name, ('#64748b', 1.5))
                                benchmarks[b_name] = (t_symbol, col_c, col_w)

                        final_values = {}
                        bench_series = {}

                        # Récupère l'historique de TOUS les indices sélectionnés en parallèle
                        # (comme le préchargement des cours en tout début de script) plutôt qu'un
                        # indice après l'autre en séquentiel : avec plusieurs indices sélectionnés
                        # et un cache froid, c'est plusieurs secondes d'attente en moins.
                        _tickers_graph = [d[0] for n, d in benchmarks.items() if n != "Mon Portefeuille"]
                        if _tickers_graph:
                            _gd_start = graph_date_debut.strftime("%Y-%m-%d")
                            _gd_end = (graph_date_fin + pd.Timedelta(days=1)).strftime("%Y-%m-%d")
                            with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(_tickers_graph))) as _ex:
                                list(_ex.map(lambda t: get_benchmark_history(t, _gd_start, _gd_end), _tickers_graph))

                        for name, data in benchmarks.items():
                            if name == "Mon Portefeuille":
                                b_perf = data[0]
                            else:
                                t_symbol = data[0]
                                try:
                                    b_hist = get_benchmark_history(
                                        t_symbol,
                                        graph_date_debut.strftime("%Y-%m-%d"),
                                        (graph_date_fin + pd.Timedelta(days=1)).strftime("%Y-%m-%d")
                                    )
                                    b_aligned = b_hist.reindex(sub_history_graph.index).ffill().bfill()
                                    if not b_aligned.empty and b_aligned.iloc[0] > 0:
                                        b_perf = ((b_aligned - b_aligned.iloc[0]) / b_aligned.iloc[0]) * 100
                                    else:
                                        b_perf = pd.Series(0.0, index=sub_history_graph.index)
                                except Exception:
                                    b_perf = pd.Series(0.0, index=sub_history_graph.index)
                        
                            bench_series[name] = b_perf
                            if not b_perf.empty:
                                final_values[name] = b_perf.iloc[-1]

                        # Résumé de la période : valeur du portefeuille aux deux dates + performance (même base que la courbe).
                        perf_port_selection = final_values.get("Mon Portefeuille")
                        _perf_sel_idx = sub_history_graph.index
                        _perf_sel_bornes = (graph_date_debut, graph_date_fin)
                        if perf_port_selection is not None and not pd.isna(perf_port_selection):
                            _val_deb_r = float(base_val)
                            _val_fin_r = float(_val_c_s.iloc[-1])
                            _gain_r = float((_val_c_s.iloc[-1] - _app_c_s.iloc[-1]) - (0.0 if _periode_complete else (base_val - base_app)))
                            _apports_r = float(_app_c_s.iloc[-1] - base_app)
                            _col_r = "#16a34a" if perf_port_selection > 0.005 else ("#dc2626" if perf_port_selection < -0.005 else "#64748b")

                            def _perf_carte(_lbl, _val, _coul, _sous=""):
                                return (f'<div style="background:{_coul}14; border:1px solid {_coul}55; border-radius:12px; padding:8px 4px; '
                                        'text-align:center; min-width:0;">'
                                        f'<div style="font-size:min(0.68rem,2.6vw); color:#64748b; text-transform:uppercase; font-weight:700; '
                                        f'letter-spacing:0.03em; line-height:1.25;">{_lbl}</div>'
                                        f'<div style="font-size:min(1.1rem,4vw); font-weight:800; color:{_coul}; margin-top:3px; line-height:1.25;">{_val}</div>'
                                        + (f'<div style="font-size:min(0.7rem,2.8vw); font-weight:600; color:{_coul};">{_sous}</div>' if _sous else '')
                                        + '</div>')

                            _perf_txt_r = f"{_arrow_sym(perf_port_selection)} {perf_port_selection:+,.2f} %".replace(",", " ").replace(".", ",")
                            _gain_txt_r = ("+" if _gain_r > 0.005 else "") + fmt_eur(_gain_r)
                            with placeholder_resume_perf.container():
                                st.markdown(
                                    '<div style="display:grid; gap:6px; margin-top:4px; grid-template-columns:repeat(3,minmax(0,1fr));">'
                                    + _perf_carte(f"Valeur au {graph_date_debut:%d/%m/%Y}", fmt_eur(_val_deb_r), "#0284c7")
                                    + _perf_carte(f"Valeur au {graph_date_fin:%d/%m/%Y}", fmt_eur(_val_fin_r), "#0284c7")
                                    + _perf_carte("Performance", _perf_txt_r, _col_r, _gain_txt_r)
                                    + '</div>',
                                    unsafe_allow_html=True,
                                )
                                if abs(_apports_r) >= 0.5:
                                    st.caption(f"ℹ️ Dont {fmt_eur(_apports_r)} d'apports nets versés pendant la période (exclus de la performance).")

                        # Longue période : on n'affiche qu'environ 600 points (un point sur N, dernier point toujours
                        # conservé) — la courbe reste fidèle mais n'est plus hachée/écrasée par des milliers de points.
                        _n_pts = len(sub_history_graph.index)
                        _pas_ds = max(1, int(np.ceil(_n_pts / 400)))
                        if _pas_ds > 1:
                            _keep_pos = sorted(set(range(0, _n_pts, _pas_ds)) | {_n_pts - 1})
                            _idx_aff = sub_history_graph.index[_keep_pos]
                            bench_series = {k: v.loc[_idx_aff] for k, v in bench_series.items()}
                        else:
                            _idx_aff = sub_history_graph.index
                        future_date = _idx_aff[-1] + pd.Timedelta(days=3)
                        extended_index = _idx_aff.append(pd.Index([future_date]))

                        sorted_curves = sorted(final_values.items(), key=lambda item: item[1], reverse=True)
                        text_positions = {}
                        last_val = None
                        collision_threshold = 8.0
                        position_state = 0

                        for name, val in sorted_curves:
                            if last_val is not None and abs(val - last_val) < collision_threshold:
                                position_state = (position_state + 1) % 4
                            else:
                                position_state = 0
                        
                            if position_state == 1:
                                text_positions[name] = "top right"
                            elif position_state == 2:
                                text_positions[name] = "bottom right"
                            elif position_state == 3:
                                text_positions[name] = "top center"
                            else:
                                text_positions[name] = "middle right"
                            last_val = val

                        fig = go.Figure()

                        for name, data in benchmarks.items():
                            color, width = data[1], data[2]
                            series = bench_series[name].round(2)
                            val_fin = round(final_values.get(name, 0), 2)
                        
                            extended_y = pd.concat([series, pd.Series([val_fin], index=[future_date])])
                            # En échelle logarithmique on trace l'indice base 100 (100 + perf %) ; le survol,
                            # lui, affiche toujours la performance en % (customdata calculé sur extended_y).
                            _y_plot = extended_y
                        
                            text_arr = [''] * len(extended_y)
                            if not pd.isna(val_fin):
                                text_str = f"&nbsp;<span style='color: {color};'><b>{_arrow_sym(val_fin)} {val_fin:+,.2f}%</b></span>".replace(",", " ").replace(".", ",")
                                text_arr[-1] = text_str

                            fig.add_trace(go.Scatter(
                                x=extended_index, y=_y_plot,
                                mode='lines+text', name=name,
                                text=text_arr,
                                textposition=text_positions.get(name, "middle right"),
                                cliponaxis=False,
                                line=dict(color=color, width=width, dash='solid'),
                                customdata=[
                                    (f"<span style='color:{'#4ade80' if v >= 0 else '#f87171'};'><b>{name}</b><br>Performance : "
                                     f"{_arrow_sym(v)} {v:+,.2f} %</span>").replace(",", " ").replace(".", ",")
                                    if not pd.isna(v) else "" for v in extended_y],
                                hovertemplate="%{customdata}<extra></extra>"
                            ))

                        fig.add_hline(
                            y=0,
                            line_dash="dash", 
                            line_color="#64748b", 
                            line_width=1.5,
                            annotation_text="0%", 
                            annotation_position="bottom right",
                            annotation_font_color="#64748b"
                        )

                        fig.update_layout(
                            paper_bgcolor='rgba(0,0,0,0)', 
                            plot_bgcolor='rgba(0,0,0,0)', 
                            hovermode="x unified", 
                            margin=dict(l=8, r=72, t=10, b=8),
                            yaxis_title="",
                            xaxis_title="",
                            height=380,
                            showlegend=False,
                            xaxis=dict(range=[dt_graph_start, future_date + pd.Timedelta(days=10)], autorange=False)
                        )
                        fig.update_yaxes(automargin=True)
                    
                        fig.update_xaxes(type="date", tickformat="%d/%m/%Y", hoverformat="%d/%m/%Y", tickangle=-45, nticks=10, showticklabels=True, automargin=True)

                        with chart_slot:
                            apply_chart_theme(fig)
                            _plotly_chart(fig, use_container_width=True, theme=None)

                        nb_curves = len(benchmarks)
                        # Toujours en colonne (vertical) : l'ancien passage en "row" (horizontal) à
                        # partir de 5 indices rendait la légende illisible en pratique. Au lieu de ça,
                        # à partir de 5 indices sélectionnés, on garde la disposition verticale mais on
                        # limite la hauteur du bloc avec une scrollbar plutôt que de tout compresser.
                        item_margin = "margin-bottom: 6px;"
                        legend_scroll_style = "max-height: 210px; overflow-y: auto; padding-right: 4px;" if nb_curves >= 5 else ""

                        legend_html_items = []
                        for name, data in benchmarks.items():
                            c_col = data[1]
                            v_end = final_values.get(name, 0.0)
                            v_end_txt = f"{_arrow_sym(v_end)} {v_end:+,.2f}".replace(",", " ").replace(".", ",")
                            legend_html_items.append(f"<div style='display: flex; justify-content: space-between; align-items: center; {item_margin} font-size: 0.85rem;'><span style='display: inline-flex; align-items: center;'><span style='height: 10px; width: 10px; background-color: {c_col}; display: inline-block; border-radius: 50%; margin-right: 6px;'></span><b style='color: #1e293b;'>{name}</b></span><span style='color: {c_col}; font-weight: bold; margin-left: 10px;'>{v_end_txt} %</span></div>")
                    
                        placeholder_legende.markdown(
                            f"""
                        <div style="font-size: 0.85rem; font-weight: 600; color: #64748b; text-transform: uppercase; letter-spacing: 0.05em; margin-bottom: 6px;">Légende</div>
                        <div style="background-color: #ffffff; border: 1px solid #e2e8f0; padding: 12px; border-radius: 8px; display: flex; flex-direction: column; {legend_scroll_style}">
                            {''.join(legend_html_items)}
                        </div>
                        """,
                            unsafe_allow_html=True
                        )
                    else:
                        st.warning("Aucune donnée disponible pour la période sélectionnée sur le graphique.")

        with st.expander("⚖️ Comparateur de performance du portefeuille par rapport aux indices", expanded=True):
            if not df_transactions.empty:
                if history_df_global is not None and not history_df_global.empty:
                    min_hist_date = history_df_global.index.min().date()
                    max_hist_date = history_df_global.index.max().date()

                    try:
                        dt_start_ts = pd.Timestamp(min_hist_date)
                        dt_end_ts = pd.Timestamp(max_hist_date)

                        tickers_benchmarks = {
                            "CAC 40": "^FCHI",
                            "MSCI World": "URTH",
                            "S&P 500": "^GSPC",
                            "Stoxx 600": "^STOXX",
                            "Nasdaq 100": "^NDX",
                            "Euro Stoxx 50": "^STOXX50E",
                            "Russell 2000": "^RUT",
                            "Emerging Markets": "EEM",
                            "Nikkei 225": "^N225"
                        }

                        sub_history = history_df_global.loc[(history_df_global.index >= dt_start_ts) & (history_df_global.index <= dt_end_ts)]
                    
                        if not sub_history.empty:
                            def get_h_val_comp(ts):
                                # Cf. get_h_val_dashboard : on renvoie aussi "Valeur Actions (€)" et
                                # "Capital Investi Total (€)" pour calculer la plus-value latente sans
                                # compter deux fois le réalisé/les dividendes (déjà présents dans la
                                # poche espèces qui compose "Valeur du Portefeuille (€)").
                                if ts in history_df_global.index:
                                    r = history_df_global.loc[ts]
                                else:
                                    idx = history_df_global.index[history_df_global.index <= ts]
                                    if len(idx) == 0:
                                        return 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
                                    r = history_df_global.loc[idx[-1]]
                                return (
                                    r["Valeur du Portefeuille (€)"], r["Apports Cumulés (€)"],
                                    r["Gain Réalisé Cumulé (€)"], r["Dividendes Cumulés (€)"],
                                    r["Valeur Actions (€)"], r["Capital Investi Total (€)"],
                                )

                            val_i, app_i, real_i, div_i, act_i, inv_i = get_h_val_comp(dt_start_ts - pd.Timedelta(seconds=1))
                            val_f, app_f, real_f, div_f, act_f, inv_f = get_h_val_comp(dt_end_ts)

                            net_real_comp = real_f - real_i
                            net_div_comp = div_f - div_i
                            net_latente_comp = (act_f - inv_f) - (act_i - inv_i)
                            gain_periode = net_latente_comp + net_real_comp + net_div_comp
                        
                            if dt_start_ts <= history_df_global.index.min():
                                perf_port_comp = perf_globale
                            else:
                                base_denom_comp = val_i if val_i > 0 else (app_i if app_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
                                perf_port_comp = (gain_periode / base_denom_comp) * 100 if base_denom_comp > 0 else 0.0

                            today_dt = _today_paris()
                            is_market_closed = today_dt.dayofweek >= 5

                            if is_market_closed:
                                perf_port_jour = "N/A"
                            else:
                                ref_today_ts = today_dt
                                ref_yesterday_ts = today_dt - pd.Timedelta(days=1)
                                val_j0, app_j0, real_j0, div_j0, act_j0, inv_j0 = get_h_val_comp(ref_today_ts)
                                val_j1, app_j1, real_j1, div_j1, act_j1, inv_j1 = get_h_val_comp(ref_yesterday_ts)
                                base_j = val_j1 if val_j1 > 0 else (app_j1 if app_j1 > 0 else (tot_invested if tot_invested > 0 else 1.0))
                                gain_jour = (act_j0 - inv_j0) - (act_j1 - inv_j1) + (real_j0 - real_j1) + (div_j0 - div_j1)
                                perf_port_jour = (gain_jour / base_j) * 100 if base_j > 0 else 0.0

                            # Semaine en cours : depuis le lundi (même logique que « mois » = depuis le 1er du mois),
                            # référence = valeur à la clôture de la veille du lundi.
                            start_week_ts = today_dt - pd.Timedelta(days=int(today_dt.dayofweek))
                            val_w_f, app_w_f, real_w_f, div_w_f, act_w_f, inv_w_f = get_h_val_comp(today_dt)
                            val_w_i, app_w_i, real_w_i, div_w_i, act_w_i, inv_w_i = get_h_val_comp(start_week_ts - pd.Timedelta(seconds=1))
                            base_w = val_w_i if val_w_i > 0 else (app_w_i if app_w_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
                            gain_w = (act_w_f - inv_w_f) - (act_w_i - inv_w_i) + (real_w_f - real_w_i) + (div_w_f - div_w_i)
                            perf_port_semaine = (gain_w / base_w) * 100 if base_w > 0 else 0.0

                            start_month_ts = pd.Timestamp(_now_paris().year, _now_paris().month, 1)
                            val_mo_f, app_mo_f, real_mo_f, div_mo_f, act_mo_f, inv_mo_f = get_h_val_comp(today_dt)
                            val_mo_i, app_mo_i, real_mo_i, div_mo_i, act_mo_i, inv_mo_i = get_h_val_comp(start_month_ts - pd.Timedelta(seconds=1))
                            base_mo = val_mo_i if val_mo_i > 0 else (app_mo_i if app_mo_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
                            gain_mo = (act_mo_f - inv_mo_f) - (act_mo_i - inv_mo_i) + (real_mo_f - real_mo_i) + (div_mo_f - div_mo_i)
                            perf_port_mois = (gain_mo / base_mo) * 100 if base_mo > 0 else 0.0

                            start_year_ts = pd.Timestamp(_now_paris().year, 1, 1)
                            val_yr_f, app_yr_f, real_yr_f, div_yr_f, act_yr_f, inv_yr_f = get_h_val_comp(today_dt)
                            val_yr_i, app_yr_i, real_yr_i, div_yr_i, act_yr_i, inv_yr_i = get_h_val_comp(start_year_ts - pd.Timedelta(seconds=1))
                            base_yr = val_yr_i if val_yr_i > 0 else (app_yr_i if app_yr_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
                            gain_yr = (act_yr_f - inv_yr_f) - (act_yr_i - inv_yr_i) + (real_yr_f - real_yr_i) + (div_yr_f - div_yr_i)
                            perf_port_annee = (gain_yr / base_yr) * 100 if base_yr > 0 else 0.0

                            _col_sel = (perf_port_selection is not None and _perf_sel_idx is not None and _perf_sel_bornes is not None)
                            comparison_data = []
                            comparison_data.append({
                                "Indice / Actif": "Mon Portefeuille",
                                "Performance du jour (%)": perf_port_jour,
                                "Performance de la semaine (%)": perf_port_semaine,
                                "Performance du mois (%)": perf_port_mois,
                                "Performance de l'année (%)": perf_port_annee,
                                "Performance globale (%)": perf_port_comp,
                                "Performance période (%)": perf_port_selection if _col_sel else np.nan
                            })

                            # Même principe que pour le graphique : on récupère l'historique des 9
                            # indices en parallèle plutôt qu'un par un, pour ne pas cumuler les
                            # temps d'attente réseau sur un cache froid.
                            _mh_start = min_hist_date.strftime("%Y-%m-%d")
                            _mh_end = (max_hist_date + pd.Timedelta(days=1)).strftime("%Y-%m-%d")
                            with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(tickers_benchmarks))) as _ex:
                                list(_ex.map(lambda t: get_benchmark_history(t, _mh_start, _mh_end), tickers_benchmarks.values()))

                            for bench_name, ticker_sym in tickers_benchmarks.items():
                                b_pers = np.nan
                                try:
                                    b_hist = get_benchmark_history(
                                        ticker_sym,
                                        min_hist_date.strftime("%Y-%m-%d"),
                                        (max_hist_date + pd.Timedelta(days=1)).strftime("%Y-%m-%d")
                                    )
                                    b_clean = b_hist.dropna()
                                
                                    if len(b_clean) >= 2 and b_clean.iloc[0] > 0:
                                        b_perf = ((b_clean.iloc[-1] - b_clean.iloc[0]) / b_clean.iloc[0]) * 100
                                    else:
                                        b_perf = 0.0

                                    if is_market_closed:
                                        b_jour = "N/A"
                                    else:
                                        if len(b_clean) >= 2:
                                            b_jour = ((b_clean.iloc[-1] - b_clean.iloc[-2]) / b_clean.iloc[-2]) * 100
                                        else:
                                            b_jour = 0.0

                                    # Semaine : depuis le lundi, par rapport à la dernière clôture avant le lundi
                                    # (à défaut, première clôture de la semaine).
                                    b_sem_apres = b_clean[b_clean.index >= start_week_ts]
                                    b_sem_avant = b_clean[b_clean.index < start_week_ts]
                                    if len(b_sem_apres) >= 1 and len(b_sem_avant) >= 1 and b_sem_avant.iloc[-1] > 0:
                                        b_sem = ((b_sem_apres.iloc[-1] - b_sem_avant.iloc[-1]) / b_sem_avant.iloc[-1]) * 100
                                    elif len(b_sem_apres) >= 2 and b_sem_apres.iloc[0] > 0:
                                        b_sem = ((b_sem_apres.iloc[-1] - b_sem_apres.iloc[0]) / b_sem_apres.iloc[0]) * 100
                                    else:
                                        b_sem = 0.0

                                    b_clean_mois = b_clean[b_clean.index >= start_month_ts]
                                    if len(b_clean_mois) >= 2 and b_clean_mois.iloc[0] > 0:
                                        b_mois = ((b_clean_mois.iloc[-1] - b_clean_mois.iloc[0]) / b_clean_mois.iloc[0]) * 100
                                    else:
                                        b_mois = 0.0

                                    b_clean_an = b_clean[b_clean.index >= start_year_ts]
                                    if len(b_clean_an) >= 2 and b_clean_an.iloc[0] > 0:
                                        b_annee = ((b_clean_an.iloc[-1] - b_clean_an.iloc[0]) / b_clean_an.iloc[0]) * 100
                                    else:
                                        b_annee = 0.0

                                    # Période sélectionnée : même méthode que la courbe du graphique (valeurs alignées sur
                                    # les jours de l'historique du portefeuille, première et dernière valeur de la période).
                                    if _col_sel:
                                        _b_sel = b_clean[(b_clean.index >= pd.Timestamp(_perf_sel_bornes[0]))
                                                         & (b_clean.index < pd.Timestamp(_perf_sel_bornes[1]) + pd.Timedelta(days=1))]
                                        _b_al = _b_sel.reindex(_perf_sel_idx).ffill().bfill()
                                        if not _b_al.empty and _b_al.iloc[0] > 0:
                                            b_pers = (_b_al.iloc[-1] / _b_al.iloc[0] - 1) * 100

                                except Exception:
                                    b_perf, b_jour, b_sem, b_mois, b_annee = 0.0, "N/A", 0.0, 0.0, 0.0

                                comparison_data.append({
                                    "Indice / Actif": bench_name,
                                    "Performance du jour (%)": b_jour,
                                    "Performance de la semaine (%)": b_sem,
                                    "Performance du mois (%)": b_mois,
                                    "Performance de l'année (%)": b_annee,
                                    "Performance globale (%)": b_perf,
                                    "Performance période (%)": b_pers
                                })

                            df_comp_res = pd.DataFrame(comparison_data)
                        
                            df_comp_res["Performance du jour"] = df_comp_res["Performance du jour (%)"].apply(lambda x: "N/A" if x == "N/A" else fmt_perf_simple(x))
                            df_comp_res["Performance de la semaine"] = df_comp_res["Performance de la semaine (%)"].apply(lambda x: fmt_perf_simple(x))
                            df_comp_res["Performance du mois"] = df_comp_res["Performance du mois (%)"].apply(lambda x: fmt_perf_simple(x))
                            df_comp_res["Performance de l'année"] = df_comp_res["Performance de l'année (%)"].apply(lambda x: fmt_perf_simple(x))
                            df_comp_res["Performance globale"] = df_comp_res["Performance globale (%)"].apply(lambda x: fmt_perf_simple(x))
                            df_comp_res["Période sélectionnée"] = df_comp_res["Performance période (%)"].apply(lambda x: fmt_perf_simple(x))
                        
                            cols_final_comp = [
                                "Indice / Actif", 
                                *(["Période sélectionnée"] if _col_sel else []),
                                "Performance du jour", 
                                "Performance de la semaine", 
                                "Performance du mois", 
                                "Performance de l'année", 
                                "Performance globale"
                            ]

                            st.markdown("#### 📊 Résultats de la Comparaison")
                            if _col_sel:
                                st.caption(f"Période sélectionnée : du {_perf_sel_bornes[0]:%d/%m/%Y} au {_perf_sel_bornes[1]:%d/%m/%Y} (dates choisies dans le graphique ci-dessus).")
                            _html_table(
                                _dash_if_empty(df_comp_res[cols_final_comp], eq_cols=tuple(cols_final_comp[1:])),
                                cell_style=lambda c, v: _style_perf_bg_cell(v) if c in cols_final_comp[1:] else "",
                            )
                        else:
                            st.warning("Aucune donnée disponible dans l'historique.")
                    except Exception as e:
                        st.error(f"Erreur lors du calcul comparatif : {e}")

# ------------------------------------------
# ONGLÊT 4 : DIVIDENDES & CARTOGRAPHIE
# ------------------------------------------
if _tab_open(tab_dividends):
    with tab_dividends:
        @_cache_render
        def _rendu_onglet_dividendes(df_port, df_transactions, pea_opening_dt, jour, market_epoch):
            with st.expander("💶 Section Dividendes & Cartographie", expanded=True):
                df_divs_pure = df_transactions[df_transactions["Type"] == "DIVIDENDE"].copy()
                if not df_divs_pure.empty:
                    df_divs_pure["Montant_Net"] = (
                        df_divs_pure["Prix Unitaire (€)"] - df_divs_pure["Commission (€)"].fillna(0) - df_divs_pure["Retenue_Source_Etrangere"].fillna(0)
                        + df_divs_pure.get("Arrondi_Courtier", pd.Series(0.0, index=df_divs_pure.index)).fillna(0)
                    )
                    df_divs_pure["Source"] = "Dividende"

                df_rompus = df_transactions[(df_transactions["Type"] == "SPLIT") & (df_transactions["Rompu"] > 0)].copy()
                if not df_rompus.empty:
                    # On date chaque rompu à sa date de versement réelle (Date_Rompus, si renseignée
                    # différemment de la date du split) plutôt qu'à la date du split : sinon il apparaît
                    # dans le mauvais mois/année de la cartographie, et un rompu pas encore versé serait
                    # compté comme "déjà perçu" alors qu'il ne l'est pas encore.
                    if "Date_Rompus" in df_rompus.columns:
                        df_rompus["Date_Heure"] = df_rompus["Date_Rompus"].fillna(df_rompus["Date_Heure"])
                    df_rompus = df_rompus[df_rompus["Date_Heure"] <= _now_paris()]
                if not df_rompus.empty:
                    df_rompus["Montant_Net"] = df_rompus["Rompu"]
                    df_rompus["Prix Unitaire (€)"] = df_rompus["Rompu"]
                    df_rompus["Retenue_Source_Etrangere"] = 0.0
                    df_rompus["Source"] = "Rompu"

                df_divs_list = [df for df in [df_divs_pure, df_rompus] if not df.empty]

                if df_divs_list:
                    df_divs = pd.concat(df_divs_list, ignore_index=True)
                    df_divs["Année"] = df_divs["Date_Heure"].dt.year
                    df_divs["Mois_Num"] = df_divs["Date_Heure"].dt.month
                    df_divs["Mois"] = df_divs["Date_Heure"].apply(lambda d: mois_fr(d, with_year=False))

                    total_div_recu = df_divs["Montant_Net"].sum()

                    render_total_card("Total Général perçu net (Div. + Rompus)", total_div_recu, "#0d9488",
                                       detail_source=df_divs, detail_value_col="Montant_Net", detail_kind="dividendes")
                    st.markdown("<div style='height:18px'></div>", unsafe_allow_html=True)
                    st.markdown("**Détail net par année :**")
                    div_yearly_sum = df_divs.groupby("Année")["Montant_Net"].sum()
                    render_yearly_amounts(div_yearly_sum, "#0d9488", detail_source=df_divs, detail_value_col="Montant_Net", detail_kind="dividendes")

                    st.markdown("<br>", unsafe_allow_html=True)
                    st.markdown("**Cartographie des dividendes mensuels :**")
                    build_calendar_heatmap(
                        df_divs, "Date_Heure", "Montant_Net",
                        ["#f0fdfa", "#0d9488"], "divs",
                        date_ouverture=(pea_opening_dt if not df_transactions.empty else None),
                        breakdown_kind="dividendes", compact=True
                    )

                    # Rendement mensuel = dividendes nets du mois ÷ capital investi moyen du mois (coût d'achat).
                    st.markdown("<p style='margin:-26px 0 0 0; font-weight:700;'>Cartographie des rendements mensuels :</p>", unsafe_allow_html=True)
                    _rows_rend = []
                    try:
                        _h_rend = get_portfolio_history(df_transactions)
                        if _h_rend is not None and not _h_rend.empty:
                            _inv_m = _h_rend["Capital Investi Total (€)"].astype(float).groupby([_h_rend.index.year, _h_rend.index.month]).mean()
                            _div_m = df_divs.groupby(["Année", "Mois_Num"])["Montant_Net"].sum()
                            for (_an_r, _mo_r), _val_r in _div_m.items():
                                _inv_r = float(_inv_m.get((int(_an_r), int(_mo_r)), 0.0))
                                if _inv_r > 0:
                                    _rows_rend.append({
                                        "Date_Heure": pd.Timestamp(year=int(_an_r), month=int(_mo_r), day=1),
                                        "Rendement": float(_val_r) / _inv_r * 100.0,
                                    })
                    except Exception:
                        _rows_rend = []
                    if _rows_rend:
                        build_calendar_heatmap(
                            pd.DataFrame(_rows_rend), "Date_Heure", "Rendement",
                            ["#f0fdfa", "#0f766e"], "rend",
                            date_ouverture=(pea_opening_dt if not df_transactions.empty else None),
                            unit="pct"
                        )
                    else:
                        st.info("Pas encore de rendement mensuel à afficher.")

                else:
                    st.info("Aucun dividende ni rompu perçu pour le moment.")

                # --- Nouvelle partie, directement sous la cartographie mensuelle des dividendes ---
                st.markdown("<hr style='margin: -22px 0 18px 0;'>", unsafe_allow_html=True)
                st.markdown("### 📅 Calendrier des dividendes à venir")

                df_divs_only_cal = df_transactions[df_transactions["Type"] == "DIVIDENDE"].copy()

                if df_divs_only_cal.empty or df_port.empty:
                    st.info("Pas encore assez d'historique de dividendes pour estimer un calendrier.")
                else:
                    tickers_detenus_cal = set(df_port[df_port["Quantité"] > 0.0001]["Ticker"])
                    name_map_div_cal = df_transactions[~df_transactions["Type"].isin(["APPORT", "RETRAIT"])].groupby("Ticker")["Nom"].last().to_dict()

                    previsions_div = []
                    occurrences_div_12m = []  # toutes les échéances estimées (pas seulement la prochaine) sur les 12 prochains mois, pour le graphique calendaire ci-dessous
                    for ticker_cal, group_cal in df_divs_only_cal.groupby("Ticker"):
                        if ticker_cal not in tickers_detenus_cal:
                            continue
                        dates_sorted_cal = group_cal["Date_Heure"].sort_values().tolist()
                        if len(dates_sorted_cal) < 1:
                            continue
                        if len(dates_sorted_cal) == 1:
                            # Un seul versement connu : on ne peut pas encore mesurer de périodicité,
                            # mais on estime tout de même la prochaine échéance en supposant un rythme
                            # annuel (le cas le plus fréquent), un an après cet unique versement — ex.
                            # un dividende perçu en juillet 2026 est projeté en juillet 2027 — plutôt que
                            # d'attendre un 2e versement avant d'afficher quoi que ce soit.
                            avg_interval_cal = 365.25
                        else:
                            intervals_cal = [(dates_sorted_cal[i] - dates_sorted_cal[i - 1]).days for i in range(1, len(dates_sorted_cal))]
                            avg_interval_cal = float(np.mean(intervals_cal))
                            if avg_interval_cal < 20:
                                # Versements trop rapprochés pour dégager une périodicité fiable
                                continue

                        last_date_cal = dates_sorted_cal[-1]
                        group_cal_sorted = group_cal.sort_values("Date_Heure")
                        montants_nets_cal = group_cal_sorted["Prix Unitaire (€)"] - group_cal_sorted["Commission (€)"].fillna(0) - group_cal_sorted["Retenue_Source_Etrangere"].fillna(0)
                        montant_moyen_cal = montants_nets_cal.mean()

                        # Taux de croissance annuel du dividende net, estimé à partir de la moyenne
                        # perçue par année (et non versement par versement, pour lisser les écarts entre
                        # les différents versements d'une même année) entre la première et la dernière
                        # année d'historique disponible : ex. si le dividende a augmenté de 10 % entre
                        # 2020 et 2026, ce taux permet de projeter une nouvelle hausse en 2027. Ce taux
                        # n'est ni stocké ni affiché nulle part : il sert uniquement, ci-dessous, à
                        # estimer un montant de versement futur plus réaliste que la moyenne historique
                        # brute lorsque l'entreprise augmente (ou baisse) régulièrement son dividende.
                        div_par_an_cal = montants_nets_cal.groupby(group_cal_sorted["Date_Heure"].dt.year).mean()
                        taux_croissance_cal = 0.0
                        if len(div_par_an_cal) >= 2 and div_par_an_cal.iloc[0] > 0:
                            nb_annees_ecart_cal = div_par_an_cal.index[-1] - div_par_an_cal.index[0]
                            if nb_annees_ecart_cal > 0:
                                taux_croissance_cal = (div_par_an_cal.iloc[-1] / div_par_an_cal.iloc[0]) ** (1 / nb_annees_ecart_cal) - 1
                                # Borné pour éviter qu'un historique trop court ou bruité ne produise une
                                # extrapolation absurde (ex. un seul gros versement exceptionnel une année).
                                taux_croissance_cal = max(-0.5, min(taux_croissance_cal, 1.0))

                        montant_dernier_cal = montants_nets_cal.iloc[-1]

                        def _montant_projete_cal(date_versement):
                            """Projette le montant net d'un versement futur en composant le taux de
                    croissance annuel estimé ci-dessus depuis le dernier versement réellement
                    perçu (plus fiable comme point de départ que la moyenne de tout l'historique,
                    surtout si le dividende a beaucoup évolué depuis les premiers versements)."""
                            annees_ecoulees = max(0.0, (date_versement - last_date_cal).days / 365.25)
                            return montant_dernier_cal * ((1 + taux_croissance_cal) ** annees_ecoulees)

                        next_date_est = last_date_cal + pd.Timedelta(days=avg_interval_cal)
                        _garde_fou = 0
                        while next_date_est < _now_paris() and _garde_fou < 50:
                            next_date_est += pd.Timedelta(days=avg_interval_cal)
                            _garde_fou += 1

                        montant_prochain_cal = _montant_projete_cal(next_date_est)

                        if avg_interval_cal > 300:
                            freq_label = "Annuelle"
                        elif avg_interval_cal > 150:
                            freq_label = "Semestrielle"
                        elif avg_interval_cal > 75:
                            freq_label = "Trimestrielle"
                        else:
                            freq_label = "Mensuelle"

                        previsions_div.append({
                            "Ticker": ticker_cal,
                            "Nom": name_map_div_cal.get(ticker_cal, ticker_cal),
                            "Prochaine date estimée": next_date_est,
                            "Montant net moyen estimé": montant_prochain_cal,
                            "Fréquence estimée": freq_label,
                        })

                        # Toutes les échéances de ce ticker tombant dans les 12 prochains mois (et non
                        # uniquement la toute prochaine), pour le graphique "12 mois de l'année" ci-dessous.
                        # Chaque échéance successive est projetée un peu plus loin dans le temps, donc la
                        # croissance estimée continue de s'y appliquer de façon composée.
                        nom_cal = name_map_div_cal.get(ticker_cal, ticker_cal)
                        occ_date = next_date_est
                        _garde_fou_occ = 0
                        # Borne alignée sur la fin du 12e mois calendaire affiché plus bas (mois_ordre),
                        # et non sur "aujourd'hui + 365 jours" pile : avec un intervalle annuel estimé à
                        # 365,25 jours (moyenne tenant compte des années bissextiles), une échéance
                        # projetée à partir d'un versement très récent (ex. un dividende perçu il y a
                        # quelques jours seulement, tout juste ajouté) tombait parfois quelques heures
                        # APRÈS "aujourd'hui + 365 jours" pile, et était donc silencieusement exclue de
                        # occurrences_div_12m : son mois n'affichait alors aucune info-bulle (ou une
                        # info-bulle incomplète, sans ce versement). La fin du 12e mois calendaire laisse
                        # systématiquement assez de marge pour l'inclure.
                        horizon_12m = (_now_paris().replace(day=1) + pd.DateOffset(months=12)) - pd.Timedelta(days=1)
                        while occ_date <= horizon_12m and _garde_fou_occ < 50:
                            occurrences_div_12m.append({
                                "Ticker": ticker_cal,
                                "Nom": nom_cal,
                                "Date": occ_date,
                                "Montant": _montant_projete_cal(occ_date),
                            })
                            occ_date += pd.Timedelta(days=avg_interval_cal)
                            _garde_fou_occ += 1

                    if not previsions_div:
                        st.info("Historique trop court (il faut au moins 2 versements passés) sur une position encore détenue : aucune estimation fiable disponible pour le moment.")
                    else:
                        df_prev_div = pd.DataFrame(previsions_div).sort_values("Prochaine date estimée")
                        today_ts_div = _now_paris()
                        total_estime_12m = df_prev_div[df_prev_div["Prochaine date estimée"] <= today_ts_div + pd.Timedelta(days=365)]["Montant net moyen estimé"].sum()

                        # Les grandes cartes détaillées par valeur (une par action, avec fréquence, badge
                        # de délai, prochaine date...) ont été retirées : avec beaucoup de lignes en
                        # portefeuille, elles surchargeaient visuellement la page. Il ne reste que le
                        # total, puis directement le graphique ci-dessous.
                        render_total_card("💰 Total estimé des dividendes à venir (12 prochains mois)", total_estime_12m, "#0d9488")

                        # --- Graphique "12 mois" : au survol de n'importe quel point d'un mois, TOUTES
                        # les entreprises versant ce mois-ci s'affichent d'un coup (et pas seulement au
                        # survol exact du petit segment de chacune). ---
                        if occurrences_div_12m:
                            st.markdown("<div style='height:18px'></div>", unsafe_allow_html=True)
                            st.markdown("**📆 Dividendes attendus sur les 12 prochains mois, par mois**")

                            mois_labels_fr = ["Janvier", "Février", "Mars", "Avril", "Mai", "Juin",
                                               "Juillet", "Août", "Septembre", "Octobre", "Novembre", "Décembre"]
                            # Abréviations utilisées pour les libellés de l'axe X (voir "labels_mois"
                            # ci-dessous). Une simple troncature à 3 lettres ("Juin"[:3] et
                            # "Juillet"[:3] valent TOUTES LES DEUX "Jui") faisait fusionner ces deux mois
                            # en une seule et même catégorie sur l'axe de Plotly dès qu'ils tombaient tous
                            # les deux dans la fenêtre de 12 mois affichée : Plotly ne peut afficher qu'une
                            # seule info-bulle pour une catégorie donnée, donc l'un des deux mois (et toute
                            # entreprise n'y versant qu'à cette date) disparaissait silencieusement du
                            # survol, tout en restant visible dans la barre empilée (d'où un mois "Vusion"
                            # dont le montant réel n'apparaissait jamais dans l'info-bulle). Cette liste
                            # dédiée garantit que les 12 mois restent toujours des catégories distinctes.
                            mois_abrev_fr = ["Jan", "Fév", "Mar", "Avr", "Mai", "Juin",
                                              "Juil", "Aoû", "Sep", "Oct", "Nov", "Déc"]
                            df_occ_12m = pd.DataFrame(occurrences_div_12m)

                            # Les 12 prochains mois calendaires en partant du mois en cours (et non
                            # forcément Janvier à Décembre), pour rester cohérent avec la fenêtre
                            # "12 prochains mois" utilisée pour le total ci-dessus.
                            mois_ordre = []
                            _cursor = _now_paris().replace(day=1)
                            for _ in range(12):
                                mois_ordre.append((_cursor.year, _cursor.month))
                                _cursor = _cursor + pd.DateOffset(months=1)

                            # Agrégation UNIQUE (mois, entreprise) -> montant total, calculée une seule
                            # fois puis relue à l'identique pour les barres ET pour l'info-bulle plus bas.
                            # Avant, les deux refiltraient séparément "df_occ_12m" par année/mois : en
                            # apparence équivalent, mais sur un mois où plusieurs entreprises versent
                            # (ex. ASML ET Vusion le même mois), l'info-bulle pouvait afficher un total et
                            # une liste incomplets (une entreprise manquante) sans que la barre empilée
                            # elle-même ne soit affectée. Les deux lisent désormais la même table agrégée :
                            # elles ne peuvent plus jamais diverger.
                            df_occ_12m["_mois_cle"] = list(zip(df_occ_12m["Date"].dt.year, df_occ_12m["Date"].dt.month))
                            agg_div_12m = df_occ_12m.groupby(["_mois_cle", "Nom"])["Montant"].sum()

                            # Graphique en barres EMPILÉES (une couleur par entreprise) plutôt qu'un
                            # simple total par mois : quand beaucoup de valeurs versent le même mois
                            # (ex. 20 actions en mai), chaque entreprise n'occupe plus qu'un petit segment
                            # de la barre du mois. Les barres elles-mêmes restent épurées (aucun nom
                            # d'entreprise, aucun mois, aucun montant écrit dessus — juste la couleur) :
                            # tout le détail vit dans une seule info-bulle par mois (voir la trace
                            # invisible "hover_overlay" ci-dessous), qui liste TOUTES les entreprises du
                            # mois survolé d'un coup, où qu'on clique sur la colonne.
                            labels_mois = [f"{mois_abrev_fr[m - 1]} {a}" for (a, m) in mois_ordre]
                            noms_uniques_12m = sorted(df_occ_12m["Nom"].unique().tolist())
                            # Palette pastel du dashboard (la même que les camemberts) au lieu des couleurs vives de Plotly.
                            palette_12m = [_alloc_color(k) for k in range(max(len(noms_uniques_12m), 1))]

                            traces_div_12m = []
                            for i, nom in enumerate(noms_uniques_12m):
                                couleur = palette_12m[i % len(palette_12m)]
                                y_vals = [float(agg_div_12m.get((mc, nom), 0.0)) for mc in mois_ordre]
                                traces_div_12m.append(go.Bar(
                                    name=nom,
                                    x=labels_mois,
                                    y=y_vals,
                                    marker=dict(color=couleur, line=dict(color="rgba(255,255,255,0.9)", width=1.5)),
                                    hoverinfo="skip",  # le détail est porté par la trace invisible ci-dessous
                                    # offsetgroup/alignmentgroup partagé avec la trace invisible ci-dessous :
                                    # sans ça, Plotly ne garantit pas que les deux occupent exactement la
                                    # même largeur de colonne, et la zone de survol de la trace invisible
                                    # pouvait être légèrement décalée par rapport à la barre réelle — ce qui
                                    # faisait rater le tooltip surtout sur les mois à très petit montant
                                    # (un dividende annuel tout juste ajouté, par exemple).
                                    offsetgroup="mois_div_12m",
                                    alignmentgroup="mois_div_12m",
                                ))

                            # Trace invisible portant l'info-bulle complète du mois (toutes les
                            # entreprises + le total, dans le format demandé), sur un axe secondaire
                            # dédié à hauteur constante (1) pour couvrir toute la hauteur du graphique
                            # quel que soit le montant réel du mois — ainsi le survol fonctionne partout
                            # sur la colonne du mois, pas seulement pile sur les segments colorés.
                            hover_mois_txt = []
                            for (an_m, mois_m) in mois_ordre:
                                mc = (an_m, mois_m)
                                # Toutes les entreprises de ce mois, lues dans la MÊME table agrégée que
                                # les barres ci-dessus (agg_div_12m) — jamais recalculées séparément.
                                try:
                                    montants_mois = agg_div_12m.xs(mc, level="_mois_cle")
                                except KeyError:
                                    montants_mois = pd.Series(dtype=float)
                                total_m = float(montants_mois.sum())
                                lignes_mois = [
                                    f"<b>{mois_labels_fr[mois_m - 1]} {an_m}</b>",
                                    f"<span style='color:#0d9488;'><b>Total : {fmt_eur(total_m)}</b></span>",
                                ]
                                if not montants_mois.empty:
                                    for nom_m, montant_m in montants_mois.sort_values(ascending=False).items():
                                        lignes_mois.append(f"{nom_m} : {fmt_eur(float(montant_m))}")
                                else:
                                    lignes_mois.append("Aucun versement attendu")
                                hover_mois_txt.append("<br>".join(lignes_mois))

                            traces_div_12m.append(go.Bar(
                                x=labels_mois, y=[1] * len(labels_mois),
                                marker=dict(color="rgba(0,0,0,0)", line=dict(width=0)),
                                # IMPORTANT : on passe le texte via "customdata" (jamais affiché sur le
                                # graphique) et non via l'attribut "text" d'un Bar, qui s'affiche par
                                # défaut DANS/SUR la barre dès qu'il est renseigné (c'est ce qui faisait
                                # apparaître le détail mois par mois écrit en clair sur le graphique,
                                # ex. en septembre). "textposition='none'" est ajouté en garde-fou
                                # supplémentaire au cas où "text" serait réintroduit par erreur plus tard.
                                customdata=hover_mois_txt,
                                textposition="none",
                                hovertemplate="%{customdata}<extra></extra>",
                                yaxis="y2",
                                showlegend=False,
                                name="",
                                offsetgroup="mois_div_12m",
                                alignmentgroup="mois_div_12m",
                            ))

                            # Total du mois écrit au-dessus de chaque barre (arrondi pour rester lisible sur téléphone).
                            _tot_mois = [float(sum(agg_div_12m.get((mc, nom), 0.0) for nom in noms_uniques_12m)) for mc in mois_ordre]
                            _fmt_tot = lambda t: ("" if t <= 0 else (f"{t:,.0f} €".replace(",", " ") if t >= 10 else f"{t:.1f} €".replace(".", ",")))
                            traces_div_12m.append(go.Scatter(
                                x=labels_mois, y=_tot_mois, mode="text",
                                text=[_fmt_tot(t) for t in _tot_mois], textposition="top center",
                                textfont=dict(size=11, color="#0f766e"),
                                hoverinfo="skip", showlegend=False, cliponaxis=False,
                            ))
                            _grid_color_div12m = "rgba(148,163,184,0.18)"
                            fig_div_12m = go.Figure(data=traces_div_12m)
                            fig_div_12m.update_layout(
                                barmode="stack",
                                height=360,
                                margin=dict(l=36, r=10, t=20, b=36),
                                bargap=0.35,
                                yaxis=dict(title=None, showgrid=True, gridcolor=_grid_color_div12m, zeroline=False,
                                           ticksuffix=" €", range=[0, max(max(_tot_mois), 1.0) * 1.2]),
                                yaxis2=dict(overlaying="y", visible=False, range=[0, 1], fixedrange=True),
                                xaxis=dict(title=None, showgrid=False, tickangle=-45 if len(labels_mois) > 8 else 0),
                                hovermode="x",
                                # Légende conservée (elle reste utile pour identifier les couleurs), même
                                # avec beaucoup d'entreprises.
                                showlegend=True,
                                legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0, font=dict(size=11)),
                            )
                            apply_chart_theme(fig_div_12m)
                            _plotly_chart(fig_div_12m, use_container_width=True, key="chart_div_12_mois")
        _rendu_onglet_dividendes(df_port, df_transactions, pea_opening_dt, _now_paris().strftime("%Y-%m-%d"), _epoch_now)


# ------------------------------------------
# ONGLÊT 5 : HISTORIQUE & SIMULATEUR
# ------------------------------------------
if _tab_open(tab_history):
    with tab_history:
        @_cache_render
        def _rendu_onglet_historique(df_transactions, tot_invested, jour, market_epoch):
            _fmt_eur_h = _fmt_eur_lecteur()

            def style_entire_row_gradient(df):
                """Dégradé à 3 paliers (vert/rouge) calculé par quantiles PROPRES à ce tableau, via
        get_quantile_level_styles — la même palette que le classement des actions par gain."""
                # Même analyse de la colonne « Performance » qu'avant, mais directement sur les valeurs
                # (plus de .iterrows() qui reconstruisait une Series par ligne), puis le tableau de styles
                # est fabriqué d'un seul bloc numpy au lieu d'un `styles.loc[ligne, :] = ...` par ligne
                # (plusieurs centaines d'affectations pandas pour le tableau quotidien). Même résultat.
                vals_list = []
                _perf_col = df["Performance"] if "Performance" in df.columns else [np.nan] * len(df)
                for _raw_val in _perf_col:
                    try:
                        val_str = str(_raw_val)
                        if "nan" in val_str.lower():
                            vals_list.append(np.nan)
                        else:
                            clean_val = (val_str.replace("▲", "").replace("▼", "").replace("▬", "")
                                         .replace("%", "").replace(" ", "").replace("+", "").replace(",", "."))
                            vals_list.append(float(clean_val))
                    except Exception:
                        vals_list.append(np.nan)
                vals_arr = np.array(vals_list, dtype=float)

                row_styles = get_quantile_level_styles(vals_arr)
                return pd.DataFrame(
                    np.repeat(np.asarray(row_styles, dtype=object).reshape(-1, 1), len(df.columns), axis=1),
                    index=df.index, columns=df.columns,
                )

            with st.expander("📅 Historique des performances quotidienne", expanded=True):
                if not df_transactions.empty:
                    history_df_quot = get_portfolio_history(df_transactions)
                    if history_df_quot is not None and not history_df_quot.empty:
                        daily_df = history_df_quot

                        # --- Version vectorisée (calculs pandas sur des colonnes entières), à la place
                        # d'une boucle Python qui tournait une fois par jour de l'historique (i.e. plus de
                        # 1300 fois) et qui, à CHAQUE jour, refiltrait l'intégralité de df_transactions
                        # (comparaison de date sur TOUTES les opérations, répétée à chaque itération) pour
                        # retrouver celles du jour : avec des centaines de transactions, ça fait des
                        # centaines de milliers de comparaisons répétées, très largement le poste le plus
                        # coûteux de tout ce tableau.
                        #
                        # Au lieu de ça : les agrégats par jour (nombre de mouvements, montant des achats,
                        # frais, apports) sont désormais calculés UNE SEULE FOIS avec un groupby pandas
                        # (vectorisé), puis simplement recherchés jour par jour (reindex) au lieu d'être
                        # recalculés à chaque itération — exactement les mêmes valeurs qu'avant, obtenues
                        # bien plus vite. Le gain/la performance du jour, qui comparait chaque ligne à la
                        # ligne précédente via des accès .iloc répétés dans la boucle, est lui aussi
                        # vectorisé avec .shift(1) (même calcul, juste sur la colonne entière d'un coup).
                        # Le formatage (_fmt_eur_h, %, mise en forme du tableau) reste identique à avant.
                        _tx_norm = df_transactions.copy()
                        _tx_norm["_jour_norm"] = _tx_norm["Date_Heure"].dt.normalize()

                        _nb_mouv_j = _tx_norm[_tx_norm["Type"].isin(["ACHAT", "VENTE"])].groupby("_jour_norm").size()
                        _achats_j = (
                            _tx_norm[_tx_norm["Type"] == "ACHAT"]
                            .assign(_montant=lambda d: d["Quantité"] * d["Prix Unitaire (€)"])
                            .groupby("_jour_norm")["_montant"].sum()
                        )
                        _ventes_j = (
                            _tx_norm[_tx_norm["Type"] == "VENTE"]
                            .assign(_montant=lambda d: d["Quantité"] * d["Prix Unitaire (€)"])
                            .groupby("_jour_norm")["_montant"].sum()
                        )
                        _frais_j = (
                            _tx_norm.groupby("_jour_norm")["Frais Totaux (€)"].sum()
                            if "Frais Totaux (€)" in _tx_norm.columns else pd.Series(dtype=float)
                        )
                        _apports_j = _tx_norm[_tx_norm["Type"] == "APPORT"].groupby("_jour_norm")["Quantité"].sum()

                        nb_mouv_s = _nb_mouv_j.reindex(daily_df.index, fill_value=0)
                        achats_s = _achats_j.reindex(daily_df.index, fill_value=0.0)
                        ventes_s = _ventes_j.reindex(daily_df.index, fill_value=0.0)
                        frais_s = _frais_j.reindex(daily_df.index, fill_value=0.0)
                        apports_s = _apports_j.reindex(daily_df.index, fill_value=0.0)

                        _cur = daily_df[[
                            "Valeur Actions (€)", "Valeur du Portefeuille (€)", "Apports Cumulés (€)",
                            "Gain Réalisé Cumulé (€)", "Dividendes Cumulés (€)", "Capital Investi Total (€)",
                        ]]
                        _prev = _cur.shift(1)
                        # Premier jour de l'historique : toutes les valeurs "de la veille" sont à 0
                        # (comme dans la boucle d'origine, où i==0 les mettait explicitement à 0.0), et
                        # non NaN comme le donnerait .shift(1) seul.
                        _prev.iloc[0] = 0.0

                        net_real_jour_s = _cur["Gain Réalisé Cumulé (€)"] - _prev["Gain Réalisé Cumulé (€)"]
                        net_div_jour_s = _cur["Dividendes Cumulés (€)"] - _prev["Dividendes Cumulés (€)"]
                        net_latente_jour_s = (
                            (_cur["Valeur Actions (€)"] - _cur["Capital Investi Total (€)"])
                            - (_prev["Valeur Actions (€)"] - _prev["Capital Investi Total (€)"])
                        )
                        gain_total_jour_s = net_latente_jour_s + net_real_jour_s + net_div_jour_s

                        # Même cascade de repli qu'avant (val_i > 0, sinon app_i > 0, sinon tot_invested,
                        # sinon 1.0) — toujours strictement positif au final, donc la division ci-dessous
                        # ne peut jamais diviser par 0.
                        _fallback_tot_inv = tot_invested if tot_invested > 0 else 1.0
                        base_denom_jour_s = _prev["Valeur du Portefeuille (€)"].where(
                            _prev["Valeur du Portefeuille (€)"] > 0,
                            _prev["Apports Cumulés (€)"].where(_prev["Apports Cumulés (€)"] > 0, _fallback_tot_inv)
                        )
                        perf_pct_jour_s = (gain_total_jour_s / base_denom_jour_s) * 100

                        # On ignore les jours totalement inactifs (week-ends, jours fériés, absence de
                        # séance, sans aucun mouvement) : sinon la table serait noyée de lignes à 0 —
                        # même condition que dans la boucle d'origine.
                        mask_actif = ~((gain_total_jour_s.abs() < 0.01) & (nb_mouv_s == 0) & (apports_s == 0))

                        if mask_actif.any():
                            df_q_res = pd.DataFrame({
                                "_dt": daily_df.index[mask_actif],
                                "Jour": daily_df.index[mask_actif].strftime("%d-%m-%Y"),
                                "Nb Mouvements": nb_mouv_s[mask_actif].to_numpy(),
                                "PV actées": net_real_jour_s[mask_actif].map(_fmt_eur_h),
                                "PV latente": net_latente_jour_s[mask_actif].map(_fmt_eur_h),
                                "Dividendes": net_div_jour_s[mask_actif].map(_fmt_eur_h),
                                "Performance": perf_pct_jour_s[mask_actif].map(fmt_perf_simple),
                                "Valeur Actions Fin Jour": _cur["Valeur Actions (€)"][mask_actif].map(_fmt_eur_h),
                                "Achats": achats_s[mask_actif].map(_fmt_eur_h),
                                "Ventes": ventes_s[mask_actif].map(_fmt_eur_h),
                                "Frais": frais_s[mask_actif].map(_fmt_eur_h),
                                "Apport": apports_s[mask_actif].map(lambda v: _fmt_eur_h(v) if v > 0 else "N/A"),
                                "_sale": daily_df.index[mask_actif].normalize().isin(
                                    pd.DatetimeIndex(df_transactions.loc[df_transactions["Type"] == "VENTE", "Date_Heure"]).normalize()
                                ),
                            }).sort_values("_dt", ascending=False).drop(columns=["_dt"])
                            # Numérotation façon "détail complet des transactions" : le jour le plus
                            # ancien affiché commence à 1, tandis que le tableau reste trié avec le jour
                            # le plus récent en haut par défaut.
                            df_q_res = df_q_res.reset_index(drop=True)
                            _total_q = len(df_q_res)
                            df_q_res.index = _total_q - df_q_res.index
                            _sale_q = df_q_res.pop("_sale").to_numpy()
                            _rs_q = _row_styles_of(style_entire_row_gradient(df_q_res))
                            _html_table(_dash_if_empty(df_q_res, eq_cols=("PV latente", "Performance"), sale_flag=_sale_q),
                                        row_styles=_rs_q, show_index=True, index_label="N°", max_height=350)
                        else:
                            st.info("Pas encore assez d'historique pour établir ce tableau.")

            with st.expander("📅 Historique des performances mensuelles", expanded=True):
                if not df_transactions.empty:
                    history_df = get_portfolio_history(df_transactions)
                    if history_df is not None:
                        monthly_df = history_df.resample('ME').last()
                        perf_records = []
                        get_h_val = _make_get_h_val(history_df)
                        _tx_agg = _make_tx_period_agg(df_transactions)
                        _sale_dts = pd.DatetimeIndex(df_transactions.loc[df_transactions["Type"] == "VENTE", "Date_Heure"])
                        _sale_ym = set(zip(_sale_dts.year, _sale_dts.month))
                        for i in range(len(monthly_df)):
                            current_date = monthly_df.index[i]
                            current_val = monthly_df.iloc[i]["Valeur Actions (€)"]
                    
                            end_of_month_dt = pd.Timestamp(current_date.year, current_date.month, current_date.days_in_month, 23, 59, 59)
                            start_of_month_dt = pd.Timestamp(current_date.year, current_date.month, 1, 0, 0, 0)
                    
                            val_f, app_f, real_f, div_f, act_f, inv_f = get_h_val(end_of_month_dt)
                            val_i, app_i, real_i, div_i, act_i, inv_i = get_h_val(start_of_month_dt - pd.Timedelta(seconds=1))
                    
                            net_real_mois = real_f - real_i
                            net_div_mois = div_f - div_i
                            net_latente_mois = (act_f - inv_f) - (act_i - inv_i)
                    
                            gain_total_mois = net_latente_mois + net_real_mois + net_div_mois
                            base_denom_mois = val_i if val_i > 0 else (app_i if app_i > 0 else (tot_invested if tot_invested > 0 else 1.0))
                            perf_pct_mois = (gain_total_mois / base_denom_mois) * 100 if base_denom_mois > 0 else 0.0

                            nb_mouv, achats_mois, frais_mois, apports_mois = _tx_agg(current_date.year, current_date.month)
                            apports_str = _fmt_eur_h(apports_mois) if apports_mois > 0 else "N/A"

                            perf_records.append({
                                "_dt": current_date,
                                "Mois": mois_fr(current_date, with_year=True),
                                "Nb Mouvements": nb_mouv,
                                "PV actées": _fmt_eur_h(net_real_mois),
                                "PV latente": _fmt_eur_h(net_latente_mois),
                                "Dividendes": _fmt_eur_h(net_div_mois),
                                "Performance": fmt_perf_simple(perf_pct_mois),
                                "Valeur Actions Fin Mois": _fmt_eur_h(current_val),
                                "Achats": _fmt_eur_h(achats_mois),
                                "Ventes": _fmt_eur_h(_tx_agg.ventes(current_date.year, current_date.month)),
                                "Frais": _fmt_eur_h(frais_mois),
                                "Apport": apports_str,
                                "_sale": (current_date.year, current_date.month) in _sale_ym,
                            })
                        df_m_res = pd.DataFrame(perf_records).sort_values("_dt", ascending=False).drop(columns=["_dt"])
                        # Numérotation façon "détail complet des transactions" : le mois le plus ancien
                        # affiché commence à 1, tableau trié avec le mois le plus récent en haut.
                        df_m_res = df_m_res.reset_index(drop=True)
                        _total_m = len(df_m_res)
                        df_m_res.index = _total_m - df_m_res.index
                        _sale_m = df_m_res.pop("_sale").to_numpy()
                        _rs_m = _row_styles_of(style_entire_row_gradient(df_m_res))
                        _html_table(_dash_if_empty(df_m_res, eq_cols=("PV latente", "Performance"), sale_flag=_sale_m),
                                    row_styles=_rs_m, show_index=True, index_label="N°", max_height=350)

            with st.expander("📅 Historique des performances annuelles", expanded=True):
                if not df_transactions.empty:
                    history_df = get_portfolio_history(df_transactions)
                    if history_df is not None:
                        yearly_df = history_df.resample('YE').last()
                        perf_year_records = []
                        _sale_years = set(pd.DatetimeIndex(df_transactions.loc[df_transactions["Type"] == "VENTE", "Date_Heure"]).year)
                        get_h_val = _make_get_h_val(history_df)
                        _tx_agg = _make_tx_period_agg(df_transactions)
                        for i in range(len(yearly_df)):
                            current_date = yearly_df.index[i]
                            current_year = current_date.year
                            current_val = yearly_df.iloc[i]["Valeur Actions (€)"]
                    
                            if current_year == _now_paris().year:
                                end_of_year_dt = pd.Timestamp(_now_paris())
                            else:
                                end_of_year_dt = pd.Timestamp(current_year, 12, 31, 23, 59, 59)
                    
                            start_of_year_dt = pd.Timestamp(current_year, 1, 1, 0, 0, 0)

                            val_f_an, app_f_an, real_f_an, div_f_an, act_f_an, inv_f_an = get_h_val(end_of_year_dt)
                            val_i_an, app_i_an, real_i_an, div_i_an, act_i_an, inv_i_an = get_h_val(start_of_year_dt - pd.Timedelta(seconds=1))
                    
                            net_real_an = real_f_an - real_i_an
                            net_div_an = div_f_an - div_i_an
                            net_latente_an = (act_f_an - inv_f_an) - (act_i_an - inv_i_an)
                    
                            gain_total_an = net_latente_an + net_real_an + net_div_an
                            base_denom_an = val_i_an if val_i_an > 0 else (app_i_an if app_i_an > 0 else (tot_invested if tot_invested > 0 else 1.0))
                            perf_pct_an = (gain_total_an / base_denom_an) * 100 if base_denom_an > 0 else 0.0

                            nb_mouv_an, achats_an, frais_an, apports_an = _tx_agg(current_year, None)
                            apports_an_str = _fmt_eur_h(apports_an) if apports_an > 0 else "N/A"
                    
                            perf_year_records.append({
                                "_year": current_year,
                                "Année": str(current_year),
                                "Nb Mouvements": nb_mouv_an,
                                "PV actées": _fmt_eur_h(net_real_an),
                                "PV latente": _fmt_eur_h(net_latente_an),
                                "Dividendes": _fmt_eur_h(net_div_an),
                                "Performance": fmt_perf_simple(perf_pct_an),
                                "Valeur Actions Fin Année": _fmt_eur_h(current_val),
                                "Achats": _fmt_eur_h(achats_an),
                                "Ventes": _fmt_eur_h(_tx_agg.ventes(current_year, None)),
                                "Frais": _fmt_eur_h(frais_an),
                                "Apport": apports_an_str,
                                "_sale": current_year in _sale_years,
                            })
                        df_y_res = pd.DataFrame(perf_year_records).sort_values("_year", ascending=False).drop(columns=["_year"])
                        # Numérotation façon "détail complet des transactions" : l'année la plus ancienne
                        # affichée commence à 1, tableau trié avec l'année la plus récente en haut.
                        df_y_res = df_y_res.reset_index(drop=True)
                        _total_y = len(df_y_res)
                        df_y_res.index = _total_y - df_y_res.index
                        _sale_y = df_y_res.pop("_sale").to_numpy()
                        _rs_y = _row_styles_of(style_entire_row_gradient(df_y_res))
                        _html_table(_dash_if_empty(df_y_res, eq_cols=("PV latente", "Performance"), sale_flag=_sale_y),
                                    row_styles=_rs_y, show_index=True, index_label="N°", max_height=350)
        _rendu_onglet_historique(df_transactions, tot_invested, _now_paris().strftime("%Y-%m-%d"), _epoch_now)


# ------------------------------------------
# ONGLÊT 6 : FRAIS (Cartographie dédiée)
# ------------------------------------------
if _tab_open(tab_fees):
    with tab_fees:
        with st.expander("🔍 Section Frais & Cartographie", expanded=True):
            df_fees_pure = df_transactions[df_transactions["Frais Totaux (€)"] > 0].copy()
        
            if not df_fees_pure.empty:
                df_fees_pure["Année"] = df_fees_pure["Date_Heure"].dt.year
                df_fees_pure["Mois_Num"] = df_fees_pure["Date_Heure"].dt.month
                df_fees_pure["Mois"] = df_fees_pure["Date_Heure"].apply(lambda d: mois_fr(d, with_year=False))

                total_fees_recu = df_fees_pure["Frais Totaux (€)"].sum()

                render_total_card("Total Général des Frais", total_fees_recu, "#f97316",
                                   detail_source=df_fees_pure, detail_value_col="Frais Totaux (€)", detail_kind="frais")
                st.markdown("<div style='height:18px'></div>", unsafe_allow_html=True)
                st.markdown("**Détail des frais par année :**")
                fees_yearly_sum = df_fees_pure.groupby("Année")["Frais Totaux (€)"].sum()
                render_yearly_amounts(fees_yearly_sum, "#f97316", detail_source=df_fees_pure, detail_value_col="Frais Totaux (€)", detail_kind="frais")

                st.markdown("<br>", unsafe_allow_html=True)
                st.markdown("**Cartographie des frais mensuels :**")
                build_calendar_heatmap(
                    df_fees_pure, "Date_Heure", "Frais Totaux (€)",
                    ["#fff7ed", "#f97316"], "fees",
                    date_ouverture=(pea_opening_dt if not df_transactions.empty else None),
                    breakdown_kind="frais"
                )
            else:
                st.info("Aucun frais enregistré pour le moment.")

# ------------------------------------------
# ONGLET WATCHLIST : actions suivies, hors portefeuille, avec zone d'achat optionnelle
# ------------------------------------------

# ------------------------------------------
# FONDAMENTAUX & ANALYSTES (Yahoo Finance) : PER / P/B / PEG, marge / ROE / dette, résultats, objectifs, recommandations
# ------------------------------------------
def _fnum(x):
    try:
        v = float(x)
        return None if (v != v or v in (float("inf"), float("-inf"))) else v
    except Exception:
        return None

@st.cache_data(ttl=6 * 3600, show_spinner=False)
def _fetch_fondamentaux(ticker):
    """Indicateurs fondamentaux et avis d'analystes d'une valeur (mis en cache 6 h). LÈVE une exception si Yahoo ne
    répond pas, pour ne jamais mémoriser un échec passager."""
    tk = yf.Ticker(ticker)
    info = None
    for _att in range(2):
        try:
            with _INFO_SEMAPHORE:
                info = tk.info
            if isinstance(info, dict) and len(info) >= 5:
                break
            info = None
        except Exception:
            info = None
        time_module.sleep(0.6)
    if info is None:
        raise RuntimeError(f"fondamentaux indisponibles pour {ticker}")
    ebitda = _fnum(info.get("ebitda"))
    dette, cash = _fnum(info.get("totalDebt")), _fnum(info.get("totalCash"))
    dn_ebitda = ((dette - (cash or 0.0)) / ebitda) if (dette is not None and ebitda and ebitda > 0) else None
    today = _today_paris().date()
    earn = None
    try:
        cal = tk.calendar
        v = cal.get("Earnings Date") if isinstance(cal, dict) else None
        if v:
            ds = sorted(pd.Timestamp(x).date() for x in (v if isinstance(v, (list, tuple)) else [v]))
            fut = [d for d in ds if d >= today]
            earn = fut[0] if fut else None
    except Exception:
        earn = None
    if earn is None:
        try:
            ts = info.get("earningsTimestamp") or info.get("earningsTimestampStart")
            if ts:
                d = datetime.fromtimestamp(float(ts)).date()
                earn = d if d >= today else None
        except Exception:
            earn = None
    reco = None
    try:
        rs = tk.recommendations_summary
        if rs is not None and len(rs) > 0:
            r0 = rs.iloc[0]
            reco = {k: int(_fnum(r0.get(k)) or 0) for k in ("strongBuy", "buy", "hold", "sell", "strongSell")}
    except Exception:
        reco = None
    return {
        "per": _fnum(info.get("trailingPE")), "pb": _fnum(info.get("priceToBook")),
        "peg": _fnum(info.get("trailingPegRatio")) or _fnum(info.get("pegRatio")),
        "marge": _fnum(info.get("profitMargins")), "roe": _fnum(info.get("returnOnEquity")),
        "dn_ebitda": dn_ebitda,
        "cible": _fnum(info.get("targetMeanPrice")), "cible_bas": _fnum(info.get("targetLowPrice")),
        "cible_haut": _fnum(info.get("targetHighPrice")), "nb_analystes": _fnum(info.get("numberOfAnalystOpinions")),
        "reco_key": str(info.get("recommendationKey") or ""), "reco_moy": _fnum(info.get("recommendationMean")),
        "prix": _fnum(info.get("currentPrice")) or _fnum(info.get("regularMarketPrice")),
        "earn": earn, "reco": reco,
    }

def _charger_fondamentaux(tickers):
    def _one(t):
        try:
            return t, _fetch_fondamentaux(t)
        except Exception:
            return t, None
    out = {}
    if not tickers:
        return out
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(8, len(tickers))) as ex:
        for t, d in ex.map(_one, tickers):
            out[t] = d
    return out

def _watchlist_get():
    """Renvoie la liste de la watchlist stockée dans la config (persistée dans config_pea.json,
    comme le reste des réglages de l'app)."""
    return list(app_config.get("watchlist", []))

def _watchlist_save(items):
    app_config["watchlist"] = items
    ok, err = save_config(app_config)
    if not ok:
        st.warning(err)
    return ok

if _tab_open(tab_watchlist):
    with tab_watchlist:
        _SENTINEL_NOUVEAU_WL = "➕ Ajouter un nouveau nom..."

        @dialog_wrapper("➕ Ajouter une valeur à la watchlist", width="large")
        def dialog_ajout_watchlist():
            # ATTENTION, contrairement à ce qu'affirmait un commentaire ici avant (retiré) : une
            # fenêtre modale (st.dialog) N'ISOLE PAS ses reruns comme un st.fragment — CHAQUE
            # interaction à l'intérieur (changer un champ, cliquer un bouton) relance tout le script
            # de l'application, y compris le rendu de tous les autres onglets. C'est justement ce qui
            # rendait "Ajouter une valeur à la watchlist" lent : voir le commentaire détaillé au
            # niveau du bouton "Ajouter à la watchlist" plus bas, qui explique le choix fait pour
            # limiter ce coût à un seul moment choisi par l'utilisateur (la fermeture) plutôt qu'à
            # chaque étape du formulaire.
            #
            # Disposition en grille 2x2 (fenêtre volontairement plus large — width="large" ci-dessus
            # — pour lui laisser la place) plutôt qu'en 3 colonnes + une rangée pleine largeur comme
            # avant : rangée 1 = "Nom de l'action / ETF" et, à sa droite, "Nom (nouveau)" quand on
            # ajoute une valeur jamais possédée (choix "➕ Ajoute...") ; rangée 2 = "Ticker" et, à sa
            # droite, "Zone d'achat (€)" — bien plus large et lisible qu'avant, elle qui tenait
            # auparavant dans un tiers de largeur seulement.
            wl_required_fields = []

            wl_r1_c1, wl_r1_c2 = st.columns(2)
            with wl_r1_c1:
                _field_label("Nom de l'action / ETF")
                with _req_field("req_wl_nom", "k_wl_nom", track=wl_required_fields):
                    choix_wl = st.selectbox(
                        "Nom de l'action / ETF",
                        options=[_SENTINEL_NOUVEAU_WL] + _all_actions_historique_precalc,
                        index=None,
                        placeholder="Choisissez une action existante ou ajoutez-en une nouvelle...",
                        key="k_wl_nom",
                        label_visibility="collapsed",
                    )

            wl_nom_val, wl_ticker_val = "", ""
            if choix_wl == _SENTINEL_NOUVEAU_WL:
                with wl_r1_c2:
                    _field_label("Nom (nouveau)")
                    with _req_field("req_wl_nom_new", "k_wl_nom_new", track=wl_required_fields):
                        wl_nom_val = st.text_input(
                            "Nom (nouveau)", key="k_wl_nom_new",
                            placeholder="Ex : LVMH", label_visibility="collapsed",
                        )

            wl_r2_c1, wl_r2_c2 = st.columns(2)
            if choix_wl == _SENTINEL_NOUVEAU_WL:
                with wl_r2_c1:
                    _field_label("Ticker")
                    with _req_field("req_wl_ticker_new", "k_wl_ticker_new", track=wl_required_fields):
                        wl_ticker_val = st.text_input(
                            "Ticker", key="k_wl_ticker_new",
                            placeholder="Ex : MC.PA", label_visibility="collapsed",
                        ).upper().strip()
            elif choix_wl is not None:
                wl_nom_val = choix_wl
                default_tick_wl = _ticker_by_name_precalc.get(wl_nom_val, "")
                with wl_r2_c1:
                    _field_label("Ticker")
                    k_tick_wl = f"k_wl_ticker__{wl_nom_val}"
                    with _req_field("req_wl_ticker", k_tick_wl, default=default_tick_wl, track=wl_required_fields):
                        wl_ticker_val = st.text_input(
                            "Ticker", value=default_tick_wl, key=k_tick_wl,
                            label_visibility="collapsed",
                        ).upper().strip()
            else:
                # Aucune action encore choisie : le champ Ticker reste affiché, désactivé et vide,
                # uniquement pour que la colonne garde la même hauteur que sa voisine "Zone d'achat".
                with wl_r2_c1:
                    _field_label("Ticker")
                    st.text_input(
                        "Ticker", value="", key="k_wl_ticker_placeholder", disabled=True,
                        placeholder="Choisissez d'abord un nom", label_visibility="collapsed",
                    )

            with wl_r2_c2:
                # Le texte "— optionnel" est retiré du libellé (cause d'un retour à la ligne qui
                # décalait le champ vers le bas et cassait l'alignement avec "Ticker") : le caractère
                # optionnel de ce champ reste signalé par l'absence de liseret rouge autour de lui
                # (contrairement à "Nom" et "Ticker", obligatoires, qui en affichent un tant qu'ils
                # sont vides) — pas besoin de le répéter en toutes lettres.
                _field_label("Zone d'achat (€)")
                wl_zone_val = st.number_input(
                    "Zone d'achat (€)", min_value=0.0, step=0.5, value=None, format="%.2f",
                    key="k_wl_zone", label_visibility="collapsed",
                )

            st.markdown('<div style="margin-top: 4px;"></div>', unsafe_allow_html=True)
            if st.button("Ajouter à la watchlist", type="primary", key="k_wl_add_btn", use_container_width=True):
                missing_wl = [k for k in wl_required_fields if st.session_state.get(k) in (None, "")]
                if missing_wl:
                    st.error("⚠️ Le nom et le ticker sont obligatoires (encadrés en rouge).")
                else:
                    _wl_items = _watchlist_get()
                    if any(it["ticker"].upper() == wl_ticker_val.upper() for it in _wl_items):
                        st.error(f"{wl_ticker_val} est déjà dans la watchlist.")
                    else:
                        _wl_items.append({
                            "ticker": wl_ticker_val,
                            "nom": wl_nom_val.strip(),
                            "zone_achat": float(wl_zone_val) if wl_zone_val else None,
                        })
                        if _watchlist_save(_wl_items):
                            # PAS de st.rerun() ici (voir plus bas pourquoi c'était le principal
                            # point lent) : l'enregistrement lui-même (écriture du fichier
                            # config_pea.json) est quasi instantané, donc dès que _watchlist_save
                            # renvoie True, la valeur EST déjà bien enregistrée — st.success()
                            # ci-dessous s'affiche immédiatement, dans la foulée du clic, sans aucun
                            # temps d'attente.
                            st.session_state["_wl_just_added_nom"] = wl_nom_val.strip()
                            for _k in ["k_wl_nom", "k_wl_nom_new", "k_wl_ticker_new", "k_wl_zone"]:
                                st.session_state.pop(_k, None)

            # Pourquoi la pop-up ne se ferme pas/ne se rafraîchit pas toute seule juste après le
            # message de succès ci-dessus : fermer une fenêtre modale Streamlit (st.dialog) exige
            # TOUJOURS un rerun complet de l'application (contrairement à ce que laissait penser le
            # commentaire plus haut sur "un st.dialog isole nativement ses reruns, comme un
            # st.fragment" — en pratique, CHAQUE interaction à l'intérieur d'une fenêtre modale,
            # y compris choisir un nom dans la liste déroulante, relance déjà tout le script, pas
            # seulement la fenêtre). Et un rerun complet réexécute AUSSI le code de rendu de TOUS
            # les autres onglets (graphiques, tableaux...) même ceux non affichés à l'écran — c'est
            # Streamlit qui fonctionne ainsi avec st.tabs() — d'où la lenteur ressentie : ce n'est
            # pas propre à la watchlist, la même chose se produit pour la fenêtre "Nouvelle
            # opération". Régler ça en profondeur demanderait de restructurer l'app pour que chaque
            # onglet ne calcule/affiche son contenu QUE lorsqu'il est réellement sélectionné, plutôt
            # que systématiquement à chaque rerun — un changement bien plus large que ce fichier
            # concerné, que je préfère ne pas improviser sans environnement pour le tester
            # réellement (même logique que pour le calcul de l'historique, déjà découpé par ticker
            # plus tôt dans cette conversation).
            #
            # En attendant, ce bouton "Ajouter" a été changé pour ne provoquer plus ce rerun complet
            # IMMÉDIATEMENT au clic : l'enregistrement et la confirmation sont instantanés, et c'est
            # seulement en fermant la pop-up (bouton ci-dessous, ou la croix en haut à droite) que le
            # rerun complet (nécessaire pour rafraîchir le tableau et fermer la fenêtre) a lieu — au
            # moment choisi par vous, pas immédiatement après avoir cliqué "Ajouter".
            _wl_just_added_nom = st.session_state.get("_wl_just_added_nom")
            if _wl_just_added_nom:
                st.success(f"✅ {_wl_just_added_nom} ajouté à la watchlist.")
                if st.button("Fermer et actualiser le tableau", key="k_wl_add_close_btn", use_container_width=True):
                    st.session_state.pop("_wl_just_added_nom", None)
                    st.rerun()

        @fragment_wrapper
        def _watchlist_tab_fragment():
            # Regroupe TOUT le contenu de l'onglet (bouton d'ajout + tableau + gestion
            # Modifier/Supprimer) dans un SEUL st.fragment, plutôt que plusieurs fragments séparés
            # comme avant : ajouter, modifier ou supprimer une valeur doit rafraîchir à la fois le
            # tableau ci-dessous ET la zone de gestion, donc les deux doivent appartenir au même
            # fragment pour se rafraîchir ensemble suite à un _rerun_scoped() (voir sa définition,
            # à côté de fragment_wrapper, tout en haut du fichier). Contrairement à une transaction
            # achat/vente (qui, elle, a bien besoin d'un st.rerun() complet pour rafraîchir
            # totaux/graphiques ailleurs dans l'app, cf. _gestion_transactions_fragment), la
            # watchlist n'a aucun impact en dehors de cet onglet : un rerun complet n'y apportait
            # rien et coûtait cher pour rien — c'est cette relance systématique et inutile de tout
            # le tableau de bord qui rendait l'ajout/la modification d'une valeur lents.
            if st.button("➕ Ajouter une valeur à la watchlist", key="wl_add_open_btn", type="primary"):
                with st.spinner("⏳ Ouverture du formulaire..."):
                    dialog_ajout_watchlist()

            watchlist_items = _watchlist_get()
            if not watchlist_items:
                st.info("Votre watchlist est vide pour le moment. Ajoutez une première valeur ci-dessus.")
                return

            # SEUIL_PROCHE_ZONE_PCT : une action est considérée "proche" de sa zone d'achat dès que
            # son prix actuel est au plus 3% au-dessus de celle-ci (encore au-dessus, mais plus pour
            # longtemps si la tendance se poursuit) — c'est ce même seuil qui alimente le message sur
            # la Vue d'ensemble.
            SEUIL_PROCHE_ZONE_PCT = 3.0

            def _wl_interp_hex(hex_a, hex_b, t):
                """Interpole linéairement entre deux couleurs hexadécimales (t=0 -> hex_a,
            t=1 -> hex_b), pour obtenir un dégradé continu plutôt que 3 paliers de couleur figés."""
                t = max(0.0, min(1.0, t))
                ra, ga, ba = int(hex_a[1:3], 16), int(hex_a[3:5], 16), int(hex_a[5:7], 16)
                rb, gb, bb = int(hex_b[1:3], 16), int(hex_b[3:5], 16), int(hex_b[5:7], 16)
                r = round(ra + (rb - ra) * t)
                g = round(ga + (gb - ga) * t)
                b = round(ba + (bb - ba) * t)
                return f"#{r:02x}{g:02x}{b:02x}"

            def _wl_row_colors(ecart_pct):
                """Calcule une couleur de fond DÉGRADÉE selon l'écart réel (et pas seulement 3 tons
            figés selon le statut) et une couleur de texte assortie, pour toute la ligne. Les
            teintes restent volontairement pastel/pâles (jamais de couleur vive) pour que le
            texte à l'intérieur reste bien lisible. Renvoie (bg_hex, texte_hex)."""
                if ecart_pct is None:
                    return "#f8fafc", "#94a3b8"
                if ecart_pct <= 0:
                    # Dans la zone : du vert le plus pâle (vient d'entrer dans la zone, écart = 0 %)
                    # au vert un peu plus soutenu mais toujours pastel (nettement en dessous de la
                    # zone, écart <= -15 %, plafonné au-delà).
                    intensite = min(abs(ecart_pct) / 15.0, 1.0)
                    return _wl_interp_hex("#f0fdf4", "#c7f3d6", intensite), "#15803d"
                elif ecart_pct <= SEUIL_PROCHE_ZONE_PCT:
                    # Proche de la zone (0 % à +3 %) : de l'ambre le plus pâle (à la limite de la
                    # zone) à un ambre un peu plus marqué (à +3 %, juste avant de sortir de "proche").
                    intensite = ecart_pct / SEUIL_PROCHE_ZONE_PCT
                    return _wl_interp_hex("#fffbeb", "#fef3c7", intensite), "#92400e"
                else:
                    # Au-dessus : s'estompe progressivement du gris le plus visible (juste au-dessus
                    # du seuil "proche") vers un gris presque blanc à partir de +25 % au-dessus de la
                    # zone (jugé "loin"), plafonné au-delà.
                    intensite = 1.0 - min((ecart_pct - SEUIL_PROCHE_ZONE_PCT) / 22.0, 1.0)
                    return _wl_interp_hex("#fcfdfe", "#eef2f6", intensite), "#64748b"

            def _wl_var_cell_html(delta_eur, pct):
                """Cellule HTML pour une colonne de variation (7j / 30j / 6 mois / 12 mois) :
            variation en € ET en % ensemble, colorée en vert (hausse) ou rouge (baisse) — "—"
            grisé si l'historique disponible ne remonte pas assez loin pour cet horizon."""
                if pct is None or delta_eur is None:
                    return '<span style="color:#94a3b8;">—</span>'
                couleur = "#15803d" if pct >= 0 else "#b91c1c"
                signe = "+" if pct >= 0 else ""
                pct_txt = f"{signe}{pct:,.1f} %".replace(",", " ").replace(".", ",")
                eur_txt = f"{signe}{delta_eur:,.2f} €".replace(",", " ").replace(".", ",")
                fleche = _arrow_sym(pct, 0.0005)
                return f'<span style="color:{couleur}; font-weight:700;">{fleche} {eur_txt} ({pct_txt})</span>'

            def _wl_jour_pct_html(pct):
                """Petit texte coloré '(+x,x %)' accolé au Prix Actuel pour la variation du jour."""
                if pct is None:
                    return ""
                couleur = "#15803d" if pct >= 0 else "#b91c1c"
                signe = "+" if pct >= 0 else ""
                pct_txt = f"{signe}{pct:,.1f} %".replace(",", " ").replace(".", ",")
                fleche = _arrow_sym(pct, 0.0005)
                return f' <span style="color:{couleur}; font-weight:700; font-size:0.88em;">({fleche} {pct_txt})</span>'

            # Badge de statut : pastille aux couleurs FIXES et contrastées (vert = dans la zone d'achat, ambre =
            # proche, gris = au-dessus), lisible quelle que soit la teinte de fond de la ligne.
            _WL_BADGES = {
                "dans":   ("🟢", "#15803d", "#ffffff"),
                "proche": ("🟡", "#f59e0b", "#3b2300"),
                "dessus": ("⚪", "#cbd5e1", "#1e293b"),
                "na":     ("➖", "#e2e8f0", "#475569"),
            }
            def _wl_badge_html(key, texte):
                _ico, _bg, _fg = _WL_BADGES.get(key, _WL_BADGES["na"])
                return (f"<span style='display:inline-block; background:{_bg}; color:{_fg}; font-weight:800; "
                        f"padding:3px 10px; border-radius:999px; font-size:0.78rem; white-space:nowrap;'>{_ico} {texte}</span>")

            wl_computed = []
            for it in watchlist_items:
                prix_actuel_wl = get_live_price(it["ticker"])
                zone_wl = it.get("zone_achat")
                ecart_pct_wl = None
                if prix_actuel_wl is not None and zone_wl:
                    ecart_pct_wl = (prix_actuel_wl - zone_wl) / zone_wl * 100
                    if ecart_pct_wl <= 0:
                        statut_wl = "Dans la zone d'achat"; statut_key_wl = "dans"
                    elif ecart_pct_wl <= SEUIL_PROCHE_ZONE_PCT:
                        statut_wl = "Proche de la zone"; statut_key_wl = "proche"
                    else:
                        statut_wl = "Au-dessus de la zone"; statut_key_wl = "dessus"
                    ecart_str_wl = f"{'+' if ecart_pct_wl >= 0 else ''}{ecart_pct_wl:,.1f} %".replace(",", " ").replace(".", ",")
                else:
                    ecart_str_wl = "—"
                    statut_wl = "Zone non définie" if not zone_wl else "Prix indisponible"; statut_key_wl = "na"
                wl_computed.append({
                    "nom": it["nom"],
                    "ticker": it["ticker"],
                    "ecart_pct": ecart_pct_wl,
                    "prix_actuel": prix_actuel_wl,
                    "zone_txt": fmt_eur(zone_wl) if zone_wl else "Non définie",
                    "ecart_txt": ecart_str_wl,
                    "statut_txt": statut_wl,
                    "statut_key": statut_key_wl,
                })

            # Tri : d'abord les valeurs avec une zone d'achat définie, de la plus proche (écart le
            # plus faible — donc déjà "Dans la zone" en tête, puisqu'un écart <= 0 y est par
            # définition) à la plus loin au-dessus ; puis, en dessous, celles sans zone d'achat
            # définie (ecart_pct=None), triées par ordre alphabétique de nom.
            wl_computed.sort(key=lambda c: (
                c["ecart_pct"] is None,
                c["ecart_pct"] if c["ecart_pct"] is not None else 0.0,
                c["nom"],
            ))

            # Affiché en tableau HTML "à la main" (plutôt qu'un st.dataframe stylé comme avant) :
            # c'est le seul moyen d'avoir, à l'intérieur d'UNE MÊME cellule, un bout de texte d'une
            # couleur différente du reste (ici, le "(+x,x %)" de la variation du jour, à côté du
            # prix) — un Styler pandas ne peut colorer qu'une cellule ENTIÈRE, jamais une partie de
            # son texte.
            _wl_cols_droite = "padding:7px 10px; text-align:right; white-space:nowrap;"
            _header_html = (
                "<tr style='border-bottom:2px solid #e2e8f0;'>"
                "<th style='padding:7px 10px; text-align:left;'>Nom</th>"
                f"<th style='{_wl_cols_droite}'>Prix Actuel</th>"
                f"<th class='hm' style='{_wl_cols_droite}'>Var. 7 jours</th>"
                f"<th class='hm' style='{_wl_cols_droite}'>Var. 30 jours</th>"
                f"<th style='{_wl_cols_droite}'>Var. 6 mois</th>"
                f"<th style='{_wl_cols_droite}'>Var. 12 mois</th>"
                f"<th class='hm' style='{_wl_cols_droite}'>Zone d'achat</th>"
                f"<th style='{_wl_cols_droite}'>Écart à la zone</th>"
                "<th style='padding:7px 10px; text-align:left;'>Statut</th>"
                "</tr>"
            )
            _lignes_wl_html = []
            _cartes_wl_html = []
            for c in wl_computed:
                bg_hex, txt_hex = _wl_row_colors(c["ecart_pct"])
                variations = get_watchlist_variations(c["ticker"])
                prix_txt = fmt_eur(c["prix_actuel"]) if c["prix_actuel"] is not None else "Indisponible"
                prix_cell_html = prix_txt + _wl_jour_pct_html(variations["jour"][1])
                badge_html = _wl_badge_html(c["statut_key"], c["statut_txt"])
                row_style = f"background-color:{bg_hex}; color:{txt_hex}; font-weight:600; border-bottom:1px solid rgba(0,0,0,0.04);"
                _lignes_wl_html.append(
                    f"<tr style='{row_style}'>"
                    f"<td style='padding:7px 10px;'>{c['nom']}</td>"
                    f"<td style='{_wl_cols_droite}'>{prix_cell_html}</td>"
                    f"<td class='hm' style='{_wl_cols_droite}'>{_wl_var_cell_html(*variations['semaine'])}</td>"
                    f"<td class='hm' style='{_wl_cols_droite}'>{_wl_var_cell_html(*variations['30j'])}</td>"
                    f"<td style='{_wl_cols_droite}'>{_wl_var_cell_html(*variations['6m'])}</td>"
                    f"<td style='{_wl_cols_droite}'>{_wl_var_cell_html(*variations['12m'])}</td>"
                    f"<td class='hm' style='{_wl_cols_droite}'>{c['zone_txt']}</td>"
                    f"<td style='{_wl_cols_droite}'>{c['ecart_txt']}</td>"
                    f"<td style='padding:7px 10px;'>{badge_html}</td>"
                    "</tr>"
                )
                # Version téléphone : une carte par valeur (nom + statut, prix, zone/écart, 4 variations en grille 2x2).
                _accent = _WL_BADGES.get(c["statut_key"], _WL_BADGES["na"])[1]
                def _mini(label, cell_html):
                    return (f"<div><div style='font-size:0.66rem; color:#64748b; font-weight:600;'>{label}</div>"
                            f"<div style='font-size:0.82rem;'>{cell_html}</div></div>")
                _cartes_wl_html.append(
                    f"<div style='background:{bg_hex}; border-left:5px solid {_accent}; border-radius:10px; "
                    f"padding:10px 12px; margin-bottom:10px; box-shadow:0 1px 2px rgba(0,0,0,0.06);'>"
                    f"<div style='display:flex; justify-content:space-between; align-items:center; gap:8px; flex-wrap:wrap;'>"
                    f"<span style='font-weight:800; font-size:0.98rem; color:#0f172a;'>{c['nom']}</span>{badge_html}</div>"
                    f"<div style='display:flex; justify-content:space-between; align-items:baseline; margin-top:6px; gap:8px; flex-wrap:wrap;'>"
                    f"<span style='font-size:1.15rem; font-weight:800; color:{txt_hex};'>{prix_cell_html}</span>"
                    f"<span style='font-size:0.78rem; color:#475569;'>Zone : <b>{c['zone_txt']}</b> · Écart : <b style='color:{txt_hex};'>{c['ecart_txt']}</b></span></div>"
                    f"<div style='display:grid; grid-template-columns:1fr 1fr; gap:6px 12px; margin-top:8px; "
                    f"padding-top:8px; border-top:1px solid rgba(0,0,0,0.08);'>"
                    f"{_mini('7 jours', _wl_var_cell_html(*variations['semaine']))}"
                    f"{_mini('30 jours', _wl_var_cell_html(*variations['30j']))}"
                    f"{_mini('6 mois', _wl_var_cell_html(*variations['6m']))}"
                    f"{_mini('12 mois', _wl_var_cell_html(*variations['12m']))}"
                    f"</div></div>"
                )

            st.markdown(
                "<style>.wl-cards{display:none;} "
                "@media (max-width: 640px){ .wl-table-wrap{display:none;} .wl-cards{display:block;} }</style>"
                "<div class='wl-table-wrap' style='overflow-x:auto;'>"
                "<table class='pea-wl' style='width:100%; border-collapse:collapse; font-size:0.9rem;'>"
                f"<thead>{_header_html}</thead>"
                f"<tbody>{''.join(_lignes_wl_html)}</tbody>"
                "</table></div>"
                f"<div class='wl-cards'>{''.join(_cartes_wl_html)}</div>",
                unsafe_allow_html=True,
            )

        _watchlist_tab_fragment()

        # --- Fondamentaux & analystes : portefeuille (positions détenues) ou watchlist ---
        @fragment_wrapper
        def _fondamentaux_fragment():
            _inject_metric_tips()
            st.markdown("<hr style='margin: 18px 0 12px 0;'>", unsafe_allow_html=True)
            st.markdown("### 📚 Fondamentaux & analystes")
            _src = "Watchlist"
            _univers = []   # (nom, ticker, valeur actuelle ou None)
            if _src == "Portefeuille":
                if df_port is not None and not df_port.empty:
                    for _, _r in df_port[df_port["Quantité"] > 0.0001].iterrows():
                        if _r.get("Ticker"):
                            _univers.append((str(_r["Nom"]), str(_r["Ticker"]), float(_r["Valeur Actuelle (€)"])))
            else:
                for _it in _watchlist_get():
                    if _it.get("ticker"):
                        _univers.append((str(_it.get("nom") or _it["ticker"]), str(_it["ticker"]), None))
            if not _univers:
                st.info("Aucune valeur à analyser pour le moment.")
                return
            with st.spinner("Chargement des données fondamentales..."):
                _data = _charger_fondamentaux(sorted({u[1] for u in _univers}))
            _ok = [(n, t, v, _data.get(t)) for (n, t, v) in _univers if _data.get(t)]
            if not _ok:
                st.warning("Données indisponibles pour le moment (Yahoo Finance ne répond pas). Réessayez dans quelques minutes.")
                return
            _fr = lambda x, d=1: f"{x:,.{d}f}".replace(",", " ").replace(".", ",")

            # 24. PER / P/B / PEG pondérés (portefeuille uniquement)
            if _src == "Portefeuille":
                with st.expander("📐 Valorisation pondérée du portefeuille", expanded=True):
                    _tot_val = sum(v for (_n, _t, v, _d) in _ok if v) or 0.0
                    def _pond(cle):
                        num = den = 0.0
                        for (_n, _t, v, d) in _ok:
                            x = d.get(cle)
                            if v and x and x > 0:
                                num += v
                                den += v / x
                        return (num / den if den > 0 else None), num
                    _cols_v = st.columns(3)
                    _cov = 0.0
                    for _c, (lbl, cle) in zip(_cols_v, [("PER pondéré", "per"), ("P/B pondéré", "pb"), ("PEG pondéré", "peg")]):
                        _val, _couv = _pond(cle)
                        _cov = max(_cov, _couv)
                        _c.metric(lbl, _fr(_val, 1) if _val is not None else "N/A")
                    if _tot_val > 0:
                        st.caption(f"Calculés sur {_cov / _tot_val * 100:.0f} % de la valeur du portefeuille (ETF et valeurs sans donnée exclus).")

            # 26. Marge, ROE et dette nette / EBITDA par ligne
            with st.expander("🏦 Qualité financière par ligne", expanded=True):
                _rows_q = []
                for (n, _t, _v, d) in _ok:
                    if d.get("marge") is None and d.get("roe") is None and d.get("dn_ebitda") is None:
                        continue
                    _rows_q.append({
                        "Nom": n,
                        "Marge nette": f"{d['marge'] * 100:.1f} %".replace(".", ",") if d.get("marge") is not None else "—",
                        "ROE": f"{d['roe'] * 100:.1f} %".replace(".", ",") if d.get("roe") is not None else "—",
                        "Dette nette / EBITDA": f"{_fr(d['dn_ebitda'], 1)}x" if d.get("dn_ebitda") is not None else "—",
                    })
                if _rows_q:
                    _NIV = ["background-color: rgba(239,68,68,0.14); color:#b91c1c; font-weight:700;",
                            "background-color: rgba(245,158,11,0.16); color:#92400e; font-weight:700;",
                            "background-color: rgba(34,197,94,0.16); color:#15803d; font-weight:700;"]
                    def _q_style(c, v):
                        t = str(v)
                        if t in ("—", ""):
                            return "color:#94a3b8;"
                        try:
                            x = float(t.replace("x", "").replace("%", "").replace(" ", "").replace(",", "."))
                        except Exception:
                            return ""
                        if c == "Marge nette":
                            return _NIV[2 if x >= 15 else (1 if x >= 5 else 0)]
                        if c == "ROE":
                            return _NIV[2 if x >= 15 else (1 if x >= 8 else 0)]
                        if c.startswith("Dette"):
                            return _NIV[2 if x <= 1.5 else (1 if x <= 3 else 0)]
                        return ""
                    _html_table(pd.DataFrame(_rows_q), cell_style=_q_style, sticky_col="Nom")
                else:
                    st.info("Aucune donnée de qualité financière disponible (ETF, ou Yahoo sans information).")

            # 25 + 28. Objectifs et recommandations des analystes
            with st.expander("🎯 Objectifs et recommandations des analystes", expanded=True):
                _RECO_FR = {"strong_buy": ("Achat fort", 2), "buy": ("Achat", 2), "hold": ("Neutre", 1),
                            "underperform": ("Vente", 0), "sell": ("Vente", 0), "strong_sell": ("Vente forte", 0)}
                _rows_a, _tri = [], []
                for (n, t, _v, d) in _ok:
                    if not d.get("cible"):
                        continue
                    px = get_live_price(t) or d.get("prix")
                    ecart = ((d["cible"] / px - 1.0) * 100.0) if px else None
                    lbl_r = _RECO_FR.get(d.get("reco_key"), ("—", None))[0]
                    nb = int(d["nb_analystes"]) if d.get("nb_analystes") else None
                    _rows_a.append({
                        "Nom": n, "Cours": fmt_eur(px) if px else "—", "Objectif moyen": fmt_eur(d["cible"]),
                        "Écart à l'objectif": fmt_perf_simple(ecart) if ecart is not None else "—",
                        "Avis": lbl_r, "Analystes": str(nb) if nb else "—",
                    })
                    _tri.append(ecart if ecart is not None else -1e9)
                if _rows_a:
                    _ord = sorted(range(len(_rows_a)), key=lambda i: -_tri[i])
                    _df_a = pd.DataFrame([_rows_a[i] for i in _ord])
                    _AV = {"Achat fort": "background-color: rgba(34,197,94,0.22); color:#15803d; font-weight:700;",
                           "Achat": "background-color: rgba(34,197,94,0.14); color:#15803d; font-weight:700;",
                           "Neutre": "background-color: rgba(148,163,184,0.20); color:#475569; font-weight:700;",
                           "Vente": "background-color: rgba(239,68,68,0.14); color:#b91c1c; font-weight:700;",
                           "Vente forte": "background-color: rgba(239,68,68,0.22); color:#b91c1c; font-weight:700;"}
                    _html_table(
                        _df_a,
                        cell_style=lambda c, v: (_style_perf_cell(v) if c == "Écart à l'objectif" else (_AV.get(str(v), "") if c == "Avis" else "")),
                        sticky_col="Nom",
                    )
                else:
                    st.info("Pas d'objectif d'analystes disponible pour ces valeurs.")

            # 27. Prochaines publications de résultats
            with st.expander("📅 Prochaines publications de résultats", expanded=True):
                _auj = _today_paris().date()
                _rows_e = sorted([(d["earn"], n) for (n, _t, _v, d) in _ok if d.get("earn")])
                if _rows_e:
                    def _dans(dt):
                        j = (dt - _auj).days
                        return "Aujourd'hui" if j == 0 else ("Demain" if j == 1 else f"Dans {j} j")
                    _df_e = pd.DataFrame([{"Nom": n, "Date": dt.strftime("%d/%m/%Y"), "Échéance": _dans(dt)} for (dt, n) in _rows_e])
                    def _e_style(c, v):
                        if c != "Échéance":
                            return ""
                        t = str(v)
                        j = 0 if t == "Aujourd'hui" else (1 if t == "Demain" else int(t.split()[1]))
                        if j <= 7:
                            return "background-color: rgba(245,158,11,0.20); color:#92400e; font-weight:700;"
                        if j <= 30:
                            return "background-color: rgba(59,130,246,0.14); color:#1d4ed8; font-weight:700;"
                        return ""
                    _html_table(_df_e, cell_style=_e_style, sticky_col="Nom")
                else:
                    st.info("Aucune date de publication annoncée pour ces valeurs.")

        _fondamentaux_fragment()

# ------------------------------------------
# ONGLET SIMULATEURS : projection de la valeur, revenu passif, retrait
# Même gabarit pour les trois : valeurs modifiables EN HAUT (champs côte à côte), résultats et courbes
# EN DESSOUS sur toute la largeur. Les cartes viennent des helpers _sim_* (CSS .pea-stat / .pea-pill).
# ------------------------------------------
PLAFOND_PEA_VERSEMENTS = 150000.0


def _color_card(label, value, color, big=False):
    """Case colorée (teinte + bordure + valeur de la couleur), utilisée côte à côte comme dans l'objectif."""
    return (f'<div style="background:{color}14; border:1px solid {color}55; border-radius:12px; padding:8px 4px; '
            'text-align:center; min-width:0; display:flex; flex-direction:column; justify-content:center;">'
            f'<div style="font-size:min({"0.74rem" if big else "0.68rem"},{"2.9vw" if big else "2.6vw"}); color:#64748b; text-transform:uppercase; '
            f'font-weight:700; letter-spacing:0.03em; line-height:1.25;">{label}</div>'
            f'<div style="font-size:min({"1.3rem" if big else "1.1rem"},{"5vw" if big else "4vw"}); font-weight:800; color:{color}; '
            f'margin-top:3px; line-height:1.25;">{value}</div></div>')


def _color_cards_row(cards):
    """Une rangée de cases colorées, toujours côte à côte (y compris sur téléphone)."""
    return (f'<div style="display:grid; gap:6px; margin-top:8px; grid-template-columns:repeat({max(len(cards), 1)},minmax(0,1fr));">'
            + "".join(cards) + "</div>")


def _fr_num(v, d=2, signed=False):
    """Nombre au format français (espace pour les milliers, virgule décimale)."""
    return f"{v:{'+' if signed else ''},.{d}f}".replace(",", " ").replace(".", ",")


def _anciennete_et_perf_annualisee():
    """(années écoulées depuis l'ouverture, performance annualisée composée). La performance est déduite de
    « Perf. Globale » (cumul depuis l'origine) ramenée à un taux ANNUEL ; 0 si l'historique fait moins de 3 mois."""
    annees = max((_now_paris() - pea_opening_dt).days / 365.25, 0.0) if not df_transactions.empty else 0.0
    if annees >= 0.25 and (1 + perf_globale / 100) > 0:
        return annees, (1 + perf_globale / 100) ** (1 / annees) - 1
    return annees, 0.0


def _apport_mensuel_moyen_hist():
    """Moyenne mensuelle des apports nets depuis l'ouverture du PEA."""
    annees = _anciennete_et_perf_annualisee()[0]
    annuel = (apports_totaux / annees) if annees >= 0.08 else apports_totaux
    return annuel / 12.0


def _apport_mensuel_defaut():
    """Apport mensuel proposé dans les simulateurs : valeur mémorisée dans la config ; à défaut l'ancienne valeur
    annuelle ÷ 12 ; à défaut la moyenne historique (arrondie à 10 €)."""
    if "apport_mensuel_projection" in app_config:
        return max(0, int(app_config["apport_mensuel_projection"]))
    if "apport_annuel_projection" in app_config:
        return max(0, int(round(float(app_config["apport_annuel_projection"]) / 12.0)))
    return max(0, int(round(_apport_mensuel_moyen_hist() / 10.0) * 10))


def _tick_labels(n):
    """3 à 4 graduations (numériques, sans unité) régulièrement réparties sur 1..n années."""
    return sorted({max(1, round(n * i / 3)) for i in range(1, 4)})


def _an_label(k):
    """« 15 ans (2041) » : durée + année d'atteinte (année en cours + k). « Aujourd'hui (2026) » pour k = 0."""
    annee = _now_paris().year + k
    if k == 0:
        return f"Aujourd'hui ({annee})"
    return (f"{k} an" if k < 2 else f"{k} ans") + f" ({annee})"


def _stacked_growth_chart(n, base, verses, interets, base_name, height=260):
    """Aires empilées : [montant de départ si `base` n'est pas None], versements cumulés, intérêts cumulés.
    Abscisses en catégories « k an(s) » (le survol affiche donc « 5 ans »), 3 à 4 repères numériques seulement."""
    cats = [_an_label(k) for k in range(n + 1)]
    ticks = _tick_labels(n)
    fig = go.Figure()
    if base is not None:
        fig.add_trace(go.Scatter(
            x=cats, y=[base] * (n + 1), name=base_name, mode="lines", stackgroup="s",
            line=dict(color="#94a3b8", width=1.5), fill="tozeroy", fillcolor="rgba(148,163,184,0.28)",
            customdata=[fmt_eur(base)] * (n + 1), hovertemplate=base_name + " : %{customdata}<extra></extra>",
        ))
    fig.add_trace(go.Scatter(
        x=cats, y=verses, name="Versements", mode="lines", stackgroup="s",
        line=dict(color="#6366f1", width=1.5), fill="tonexty" if base is not None else "tozeroy",
        fillcolor="rgba(99,102,241,0.30)",
        customdata=[fmt_eur(v) for v in verses],
        hovertemplate="<span style='color:#a5b4fc;'>●</span> <span style='color:#a5b4fc;'>Versements cumulés : <b>%{customdata}</b></span><extra></extra>",
    ))
    fig.add_trace(go.Scatter(
        x=cats, y=[max(i, 0.0) for i in interets], name="Intérêts", mode="lines", stackgroup="s",
        line=dict(color="#10b981", width=2.2), fill="tonexty", fillcolor="rgba(16,185,129,0.30)",
        customdata=[fmt_eur(v) for v in interets],
        hovertemplate="<span style='color:#6ee7b7;'>●</span> <span style='color:#6ee7b7;'>Intérêts cumulés : <b>%{customdata}</b></span><extra></extra>",
    ))
    fig.update_layout(
        height=height, margin=dict(l=8, r=12, t=6, b=6), hovermode="x unified", showlegend=False,
        yaxis=dict(title="", rangemode="tozero", tickformat=".2s", ticksuffix=" €", nticks=4, automargin=True),
        xaxis=dict(title="", type="category", tickmode="array", tickvals=[cats[k] for k in ticks],
                   ticktext=[cats[k] for k in ticks], tickangle=0, tickfont=dict(size=10), showgrid=False),
    )
    apply_chart_theme(fig)
    return fig


@fragment_wrapper
def _render_sim_epargne(valeur_depart):
    """Simulateur unique « épargne & revenu passif » (regroupe l'ancienne projection de valeur et l'ancien
    simulateur de revenu passif, qui partageaient la même mécanique) : croissance d'abord, versements en fin
    d'année, versements bornés par le plafond du PEA (150 000 €). Résultats : valeur brute, valeur nette (impôt sur
    l'ensemble des intérêts, en pouvoir d'achat d'aujourd'hui) et revenu passif mensuel."""
    st.markdown("### 📈 Simulateur d'épargne & de revenu passif")
    with st.expander("🔮 Valeur du portefeuille, valeur nette et revenu passif", expanded=True):
        annees_ecoulees, perf_annualisee = _anciennete_et_perf_annualisee()
        moy_mensuel = _apport_mensuel_moyen_hist()
        _default_perf_hist = round(perf_annualisee * 100, 2) if perf_annualisee > 0 else 7.0

        # ---- Valeurs modifiables (en haut) : un seul jeu de paramètres pour tous les résultats
        with st.container(border=True):
            with st.container(key="compact_cols_proj"):
                c1, c2 = st.columns(2)
                pf0 = c1.number_input(
                    "Portefeuille actuel (€)", min_value=0.0, step=1000.0, format="%.0f",
                    value=float(max(round(valeur_depart), 0)), key="k_rp_depart",
                )
                apport_mensuel = c2.number_input(
                    "Apport prévu par mois (€)", min_value=0, step=10, format="%d",
                    value=_apport_mensuel_defaut(), key="k_apport_mensuel_projection",
                    help="Ajouté chaque mois (cumulé et versé en fin d'année dans la simulation), en plus de la croissance du portefeuille.",
                )
                c3, c4 = st.columns(2)
                horizon_annees = c3.number_input(
                    "Nombre d'années", min_value=1, max_value=50, step=1, format="%d",
                    value=int(app_config.get("horizon_projection_annees", 10)), key="k_horizon_projection",
                )
                perf_annuelle_proj_pct = c4.number_input(
                    "Performance annuelle retenue (%)", min_value=-50.0, max_value=100.0, step=0.5, format="%.2f",
                    value=float(app_config.get("perf_annuelle_projection", _default_perf_hist)),
                    key="k_perf_annuelle_projection",
                    help="Utilisée pour faire croître le portefeuille d'une année sur l'autre.",
                )
                c5, c6 = st.columns(2)
                impot = c5.number_input(
                    "Imposition des gains (%)", min_value=0.0, max_value=100.0, step=0.1,
                    value=float(app_config.get("taux_prelevements_sociaux", 18.6)), key="k_rp_impot",
                    help="Par défaut : le taux de prélèvements sociaux réglé dans l'application, appliqué aux gains au moment du "
                         "retrait. Si le PEA a moins de 5 ans à ce moment-là (ancienneté actuelle + nombre d'années), "
                         "12,8 % d'impôt sur le revenu sont ajoutés automatiquement.",
                )
                infl = c6.number_input(
                    "Inflation (%)", min_value=0.0, max_value=20.0, step=0.1, value=2.0, key="k_rp_infl",
                    help="La valeur finale et le revenu passif sont exprimés en euros d'aujourd'hui (pouvoir d'achat). Mettez 0 pour les voir sans inflation.",
                )
                c7, _c8 = st.columns(2)
                taux_ret = c7.number_input(
                    "Taux de retrait (%)", min_value=0.0, max_value=20.0, step=0.25, value=4.0, key="k_rp_retrait",
                    help="Part du capital net retirée chaque année pour le revenu passif.",
                )
            _fiable = "" if annees_ecoulees >= 1 else " ⚠️ historique court, peu fiable"
            st.caption(
                f"Apports moyens depuis l'ouverture du PEA : **{fmt_eur(moy_mensuel)} / mois**  \n"
                f"Performance moyenne depuis l'ouverture : **{_arrow_sym(perf_annualisee)} {_fr_num(perf_annualisee * 100, 2, signed=True)} % / an**.{_fiable}"
            )
        if horizon_annees != int(app_config.get("horizon_projection_annees", 10)):
            app_config["horizon_projection_annees"] = int(horizon_annees)
            _ok1, _err1 = save_config(app_config)
            if not _ok1:
                st.warning(_err1)
        if apport_mensuel != _apport_mensuel_defaut():
            app_config["apport_mensuel_projection"] = int(apport_mensuel)
            app_config.pop("apport_annuel_projection", None)
            _ok2, _err2 = save_config(app_config)
            if not _ok2:
                st.warning(_err2)
        if round(perf_annuelle_proj_pct, 2) != round(float(app_config.get("perf_annuelle_projection", _default_perf_hist)), 2):
            app_config["perf_annuelle_projection"] = float(perf_annuelle_proj_pct)
            _ok3, _err3 = save_config(app_config)
            if not _ok3:
                st.warning(_err3)

        # ---- Calcul année par année (croissance, puis versements de l'année, plafonnés à 150 000 € d'apports nets)
        n = int(horizon_annees)
        inv = apport_mensuel * 12.0
        r = perf_annuelle_proj_pct / 100.0
        f = 1.0 + infl / 100.0
        verses0 = min(max(float(apports_totaux), 0.0), pf0)   # point de départ : versements actuels du portefeuille
        vals, verses = [pf0], [verses0]
        ap_cur = float(apports_totaux)
        for _k in range(1, n + 1):
            place_restante = max(PLAFOND_PEA_VERSEMENTS - ap_cur, 0.0)
            ap_annee = min(inv, place_restante)
            vals.append(vals[-1] * (1 + r) + ap_annee)
            ap_cur += ap_annee
            verses.append(verses[-1] + ap_annee)
        interets = [v - vs for v, vs in zip(vals, verses)]
        # Valeurs corrigées de l'inflation (€ d'aujourd'hui) année par année ; avec une inflation de 0 %, ce sont les
        # valeurs brutes. Le graphique et la case « Valeur dans N ans » utilisent ces valeurs.
        reelles = [v / f ** k for k, v in enumerate(vals)]
        valeur_brute = vals[-1]
        valeur_reelle = reelles[-1]
        interets_reels = [max(rv - vs, 0.0) for rv, vs in zip(reelles, verses)]
        # Imposition AU MOMENT DU RETRAIT, selon l'ancienneté du PEA à cette date (ancienneté actuelle + horizon) :
        # 5 ans et plus -> prélèvements sociaux seulement ; moins de 5 ans -> + 12,8 % d'impôt sur le revenu.
        _anciennete_fin = float(annees_ecoulees) + n
        _taux_impot_retrait = float(impot) + (0.0 if _anciennete_fin >= 5 else 12.8)
        _gains_finaux = max(valeur_brute - verses[-1], 0.0)
        valeur_nette_impots = valeur_brute - _gains_finaux * _taux_impot_retrait / 100.0
        revenu_mensuel_brut = valeur_reelle * taux_ret / 100.0 / 12.0
        revenu_mensuel_net = (valeur_nette_impots / f ** n) * taux_ret / 100.0 / 12.0
        apports_cumules_finaux = min(ap_cur, PLAFOND_PEA_VERSEMENTS)

        # Échéance d'atteinte du plafond au rythme de l'apport prévu (versement continu et régulier).
        montant_restant_plafond = PLAFOND_PEA_VERSEMENTS - apports_totaux
        annees_avant_plafond = None
        if montant_restant_plafond <= 0:
            date_plafond_str = "Déjà atteint"
        elif inv > 0:
            annees_avant_plafond = montant_restant_plafond / inv
            date_plafond_str = (_now_paris() + pd.Timedelta(days=annees_avant_plafond * 365.25)).strftime("%d/%m/%Y")
        else:
            date_plafond_str = "Jamais (aucun apport prévu)"

        # ---- Résultats (en dessous)
        _sim_headline_duo([
            ("Valorisation", fmt_eur(valeur_reelle), "", True, "#0284c7"),
        ])
        _sim_headline_duo([
            ("Revenu passif / mois", fmt_eur(revenu_mensuel_brut), "avant impôts", False),
            ("Revenu passif / mois net d'impôts", fmt_eur(revenu_mensuel_net),
             "", True, "#16a34a"),
        ])
        _sim_headline_duo([
            ("Versements cumulés", fmt_eur(verses[-1]), "", False, "#6366f1"),
            ("Intérêts", fmt_eur(max(valeur_reelle - verses[-1], 0.0)), "", False, "#10b981"),
        ])
        interets_chart = interets_reels
        fig_sim = _stacked_growth_chart(n, None, verses, interets_chart, "")
        _plotly_chart(fig_sim, use_container_width=True, theme=None, key="chart_sim_epargne")

        # Plafond de versements : la barre reflète les apports cumulés PROJETÉS en fin d'horizon.
        pct_plafond = min(max((apports_cumules_finaux / PLAFOND_PEA_VERSEMENTS) * 100, 0.0), 100.0)
        grad_plafond = "linear-gradient(90deg, #d97706, #fbbf24)" if pct_plafond < 90 else "linear-gradient(90deg, #dc2626, #f87171)"
        st.markdown(
            '<div style="margin-top: -12px; padding: 12px 14px; background:#f8fafc; border:1px solid #e2e8f0; border-radius:10px;">'
            '<div style="display:flex; justify-content:space-between; align-items:baseline; flex-wrap:wrap; gap:4px; margin-bottom:8px;">'
            '<div style="font-size:0.74rem; color:#64748b; text-transform:uppercase; font-weight:700; letter-spacing:0.04em;">🏦 Plafond de versements PEA</div>'
            f'<div style="font-size:0.82rem; font-weight:700; color:#0f172a;">{fmt_eur(apports_cumules_finaux)} / {fmt_eur(PLAFOND_PEA_VERSEMENTS)}</div></div>'
            '<div style="background:#e2e8f0; border-radius:999px; height:12px; overflow:hidden;">'
            f'<div style="width:{pct_plafond}%; height:100%; background:{grad_plafond}; border-radius:999px;"></div></div>'
            '<div style="margin-top:8px; font-size:0.78rem; color:#475569;">'
            f'📅 Date de plafonnement selon les valeurs saisies : <b style="color:#0f172a;">{date_plafond_str}</b></div></div>',
            unsafe_allow_html=True,
        )
        if annees_avant_plafond is not None and 0 <= annees_avant_plafond <= n and inv > 0:
            st.caption(f"⚠️ Au rythme prévu, le plafond de versements du PEA ({fmt_eur(PLAFOND_PEA_VERSEMENTS)}) serait atteint avant la fin de l'horizon : les apports sont plafonnés à partir de cette échéance.")
        st.markdown("<div style='height:1.5rem;'></div>", unsafe_allow_html=True)


def _render_sim_retrait():
    """Simulateur de retrait PEA : part de capital / de plus-value, prélèvements sociaux, impôt (PEA < 5 ans), net perçu."""
    st.markdown("### 🧮 Simulateur de Retrait")
    with st.expander("💸 Simulation d'un retrait", expanded=True):
        # Le taux de prélèvements sociaux peut évoluer (lois de finances) : il est éditable et mémorisé dans la config.
        current_taux_ps_val = float(app_config.get("taux_prelevements_sociaux", 18.6))
        with st.container(border=True):
            st.markdown("**💰 Paramètres du retrait**")
            with st.container(key="compact_cols_retrait"):
                col_mt, col_ps = st.columns(2)
                montant_retrait_souhaite = col_mt.number_input(
                    "Montant souhaité (€)", min_value=0.0, step=500.0, value=None,
                    placeholder="Entrez un montant...", key="k_sim_retrait_montant",
                )
                taux_ps_pct = col_ps.number_input(
                    "Prélèvements sociaux (%)", min_value=0.0, max_value=100.0, step=0.1, format="%.1f",
                    value=current_taux_ps_val, key="k_sim_retrait_taux_ps",
                    help="Taux en vigueur au moment du retrait. Modifiable si la réglementation évolue : la valeur saisie est mémorisée automatiquement.",
                )
            age_plan_plus_5 = st.checkbox(
                "Le PEA a plus de 5 ans", value=True, key="k_sim_retrait_pea_5ans",
                help="Un PEA de plus de 5 ans est exonéré d'impôt sur le revenu sur les plus-values (seuls les prélèvements sociaux restent dus).",
            )
        if taux_ps_pct != current_taux_ps_val:
            app_config["taux_prelevements_sociaux"] = float(taux_ps_pct)
            _ok_ps, _err_ps = save_config(app_config)
            if not _ok_ps:
                st.warning(_err_ps)

        if not age_plan_plus_5:
            st.caption("⚠️ Avant 5 ans, un retrait (même partiel) clôture le PEA et l'ensemble des gains est imposé (12,8 % + prélèvements sociaux) : "
                       "cette simulation ne calcule que la part de gain contenue dans le montant retiré.")

        if not (montant_retrait_souhaite is not None and montant_retrait_souhaite > 0):
            st.markdown(
                '<div style="padding: 28px 20px; background:#f8fafc; border:1px dashed #cbd5e1; border-radius:12px; text-align:center; color:#64748b;">'
                '<div style="font-size:1.6rem;">🧮</div>'
                '<div style="font-size:0.92rem; font-weight:600; margin-top:6px;">Saisissez un montant de retrait pour voir la simulation</div>'
                '<div style="font-size:0.8rem; margin-top:4px;">La répartition capital / plus-value, les taxes et le net perçu s\'afficheront ici.</div></div>',
                unsafe_allow_html=True,
            )
            return

        # Base réglementaire (BOFiP) : la part de plus-value d'un retrait se calcule sur la VALEUR TOTALE DU PLAN
        # (actions + espèces) rapportée aux VERSEMENTS NETS CUMULÉS (apports - retraits).
        valeur_totale_pea = tot_value_globale
        ratio_pv = max(0.0, (valeur_totale_pea - apports_totaux) / valeur_totale_pea) if valeur_totale_pea > 0 else 0.0
        part_pv = montant_retrait_souhaite * ratio_pv
        part_capital = montant_retrait_souhaite - part_pv
        montant_ps = part_pv * (taux_ps_pct / 100.0)
        montant_ir = 0.0 if age_plan_plus_5 else part_pv * 0.128
        total_taxes = montant_ps + montant_ir
        net_recu = montant_retrait_souhaite - total_taxes

        part_capital_pct = part_capital / montant_retrait_souhaite * 100
        part_pv_pct = 100.0 - part_capital_pct
        net_pct = net_recu / montant_retrait_souhaite * 100
        if net_pct >= 90:
            grad_color, net_color = "linear-gradient(90deg, #16a34a, #4ade80)", "#16a34a"
        elif net_pct >= 80:
            grad_color, net_color = "linear-gradient(90deg, #0284c7, #38bdf8)", "#0284c7"
        else:
            grad_color, net_color = "linear-gradient(90deg, #d97706, #fbbf24)", "#d97706"

        _fr = lambda v, d=1: _fr_num(v, d)
        st.markdown(
            _color_cards_row([
                _color_card("💵 Montant net perçu", fmt_eur(net_recu), net_color, big=True),
                _color_card("Total fiscalité", fmt_eur(total_taxes), "#dc2626" if total_taxes > 0 else "#64748b", big=True),
            ])
            + '<div style="height:8px;"></div>'
            + _progress_bar_html(net_pct, grad_color, net_color, f"{_fr(net_pct)} % conservés après fiscalité")
            + _color_cards_row([
                _color_card("Montant demandé", fmt_eur(montant_retrait_souhaite), "#0284c7"),
                _color_card(f"Dont capital ({_fr(part_capital_pct, 2)} %)", fmt_eur(part_capital), "#4f46e5"),
                _color_card(f"Dont plus-value ({_fr(part_pv_pct, 2)} %)", fmt_eur(part_pv), "#10b981"),
            ])
            + _color_cards_row(
                [_color_card(f"Prélèvements sociaux ({_fr(taux_ps_pct)} %)", fmt_eur(montant_ps), "#d97706")]
                + ([] if age_plan_plus_5 else [_color_card("Impôt sur le revenu (12,8 %)", fmt_eur(montant_ir), "#dc2626")])
            )
            + '<div style="height:22px;"></div>',   # ligne vide avant le bas de la section
            unsafe_allow_html=True,
        )

if _tab_open(tab_simulateur):
    with tab_simulateur:
        _render_sim_epargne(float(tot_value_globale))
        _render_sim_retrait()
