"""
doc_import.py — lecture de documents de courtier pour pré-remplir le formulaire "Nouvelle opération".

Deux niveaux :
  1) parse_document()    : règles déterministes (gratuit, instantané, exact) pour les documents
                           Boursorama : avis d'opéré, relevé de coupons/dividendes, avis d'opération
                           sur titres (attribution gratuite / regroupement), relevé de compte espèces
                           (virements = apports/retraits).
  2) parse_with_llm()    : repli "intelligent" pour tout autre document (autre courtier, format
                           inconnu, scan) via l'API Anthropic. Facultatif : nécessite la clé
                           ANTHROPIC_API_KEY dans st.secrets et le paquet `anthropic`.

Le module ne dépend PAS de Streamlit (testable seul). Dépendance : pdfplumber.
"""
from __future__ import annotations

import io
import json
import re
import unicodedata
from dataclasses import dataclass, field, asdict
from datetime import date, time, datetime
from difflib import SequenceMatcher
from typing import Optional

import pdfplumber

OP_TYPES = ("ACHAT", "VENTE", "DIVIDENDE", "SPLIT", "APPORT", "RETRAIT")


# ----------------------------------------------------------------------------------------------
# Modèle de données
# ----------------------------------------------------------------------------------------------
@dataclass
class ParsedOp:
    type: str                                  # ACHAT / VENTE / DIVIDENDE / SPLIT / APPORT / RETRAIT
    date: Optional[date] = None
    time: Optional[time] = None                # heure d'exécution (achat/vente uniquement)
    name: str = ""                             # libellé de la valeur tel qu'affiché par le courtier
    isin: str = ""
    quantity: Optional[float] = None           # titres (achat/vente/dividende)
    price: Optional[float] = None              # cours exécuté (achat/vente)
    commission: Optional[float] = None
    ttf: Optional[float] = None
    amount: Optional[float] = None             # apport / retrait / dividende BRUT
    withholding: Optional[float] = None        # retenue à la source (dividende)
    capital_repayment: Optional[float] = None  # remboursement de capital (dividende)
    factor: Optional[float] = None             # facteur split (1,1 = 1 nouvelle pour 10 anciennes)
    label: str = ""                            # description courte affichée dans la liste
    notes: list = field(default_factory=list)  # avertissements à montrer à l'utilisateur

    def to_dict(self):
        d = asdict(self)
        d["date"] = self.date.isoformat() if self.date else None
        d["time"] = self.time.strftime("%H:%M:%S") if self.time else None
        return d


@dataclass
class ParseResult:
    doc_type: str = "inconnu"                  # avis_opere / coupons / ost / releve_especes / ...
    doc_label: str = ""
    ops: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    method: str = "regles"                     # "regles" ou "ia"
    recognized: bool = False


# ----------------------------------------------------------------------------------------------
# Extraction du texte PDF
# ----------------------------------------------------------------------------------------------
# Certains PDF Boursorama (relevés de compte 2026) ont une table de caractères défectueuse : é -> Ø, è -> Ł
_MOJIBAKE = str.maketrans({"Ø": "é", "Ł": "è", "ß": "û"})


def _clean(s: str) -> str:
    return (s or "").translate(_MOJIBAKE)


def extract_pages(data: bytes):
    """Retourne une liste de pages : {"lines": [str], "words": [dict pdfplumber]}.
    x_tolerance=1 : indispensable, sinon les PDF anciens (2021-2022) perdent les espaces."""
    pages = []
    with pdfplumber.open(io.BytesIO(data)) as pdf:
        for p in pdf.pages:
            text = p.extract_text(x_tolerance=1) or ""
            lines = [_clean(l) for l in text.split("\n") if "(cid:" not in l]
            words = p.extract_words(x_tolerance=1) or []
            for w in words:
                w["text"] = _clean(w["text"])
            pages.append({"lines": lines, "words": words})
    return pages


def pages_to_text(pages) -> str:
    return "\n".join("\n".join(p["lines"]) for p in pages)


def _norm(s: str) -> str:
    """Majuscules, sans accents ni ponctuation ni espaces : pour comparer des libellés."""
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^A-Z0-9]", "", s.upper())


# ----------------------------------------------------------------------------------------------
# Utilitaires nombres / dates
# ----------------------------------------------------------------------------------------------
_NUM_RE = re.compile(r"-?\d{1,3}(?:[ \u00a0.]\d{3})*,\d+|-?\d+,\d+")


def _num(s: str) -> float:
    s = s.replace("\u00a0", "").replace(" ", "")
    # séparateur de milliers "." (relevés 2026) ou " " (anciens) ; décimale ","
    s = s.replace(".", "").replace(",", ".")
    return float(s)


def _nums(line: str):
    return [_num(m.group(0)) for m in _NUM_RE.finditer(line)]


def _d(s: str) -> date:
    return datetime.strptime(s, "%d/%m/%Y").date()


def _t(s: str) -> time:
    return datetime.strptime(s, "%H:%M:%S").time()


# ----------------------------------------------------------------------------------------------
# Classification
# ----------------------------------------------------------------------------------------------
def classify(text: str) -> str:
    n = _norm(text)
    if "OPERATIONDEBOURSE" in n:
        return "avis_opere"
    if "COUPONSREMBOURSEMENTS" in n:
        return "coupons"
    if "AVISDEREALISATION" in n:
        return "ost_realisation"
    if "AVISDOPERATIONSURTITRES" in n or "AVISDOPERATIONSURTITRE" in n:
        return "ost"
    if "RELEVECOMPTEESPECES" in n or "EXTRAITDEVOTRECOMPTEENEUR" in n:
        return "releve_especes"
    if "RELEVECOMPTETITRES" in n:
        return "releve_titres"
    if "MIFID" in n and "FRAIS" in n:
        return "releve_frais"
    return "inconnu"


_DOC_LABELS = {
    "avis_opere": "Avis d'opéré",
    "coupons": "Relevé de coupons / dividendes",
    "ost": "Avis d'opération sur titres",
    "ost_realisation": "Avis de réalisation (opération sur titres)",
    "releve_especes": "Relevé de compte espèces",
    "releve_titres": "Relevé de compte titres",
    "releve_frais": "Relevé annuel de frais",
    "inconnu": "Document non reconnu",
}


# ----------------------------------------------------------------------------------------------
# Avis d'opéré (achat / vente)
# ----------------------------------------------------------------------------------------------
_QTY = r"(\d{1,3}(?:[ \u00a0]\d{3})+(?:,\d+)?|\d+(?:,\d+)?)"
_EXEC_RE = re.compile(r"^(\d{2}/\d{2}/\d{4})\s+" + _QTY + r"\s+(.+?)\s+R[ée]f[ée]rence\s*:", re.I)
_TIME_RE = re.compile(r"\b(\d{2}:\d{2}:\d{2})\b")
_ISIN_RE = re.compile(r"\b([A-Z]{2}[A-Z0-9]{9}\d)\b")
_COURS_RE = re.compile(r"Cours\s*ex[ée]cut[ée]\s*:\s*(\d+(?:[ .]\d{3})*(?:,\d+)?)\s*([A-Z]{3})?", re.I)


def parse_avis_opere(pages) -> ParseResult:
    res = ParseResult("avis_opere", _DOC_LABELS["avis_opere"], recognized=True)
    lines = [l for p in pages for l in p["lines"]]
    text_n = _norm("\n".join(lines))

    if "VENTECOMPTANT" in text_n:
        op_type = "VENTE"
    elif "ACHATCOMPTANT" in text_n:
        op_type = "ACHAT"
    else:
        res.recognized = False
        res.warnings.append("Avis d'opéré reconnu, mais ni achat ni vente comptant détecté (autre type d'ordre ?).")
        return res

    op = ParsedOp(type=op_type)
    for i, l in enumerate(lines):
        m = _EXEC_RE.match(l)
        if m:
            op.date = _d(m.group(1))
            op.quantity = _num(m.group(2))  # gère "6 000"
            op.name = m.group(3).strip(" .")
            # l'heure est sur la ligne suivante ou la suivante-suivante ("Type d'ordre : au marché 11:02:36")
            for j in range(i, min(i + 4, len(lines))):
                mt = _TIME_RE.search(lines[j])
                if mt:
                    op.time = _t(mt.group(1))
                    break
            break

    for l in lines:
        mi = _ISIN_RE.search(l)
        if mi and "ISIN" in _norm(l):
            op.isin = mi.group(1)
        mc = _COURS_RE.search(l)
        if mc:
            op.price = _num(mc.group(1))
            if mc.group(2) and mc.group(2) != "EUR":
                op.notes.append(f"Cours exprimé en {mc.group(2)} : vérifiez le prix unitaire en euros.")

    # montant net (dernière ligne "Montant net au débit/crédit de votre compte")
    net = None
    for i, l in enumerate(lines):
        if "MONTANTNETAU" in _norm(l):
            # domestique : valeurs sur la ligne suivante (le net est le dernier nombre)
            # étranger   : "Montant net au débit de votre compte" puis ligne suivante = le net seul
            cand = _nums(lines[i + 1]) if i + 1 < len(lines) else []
            if cand:
                net = cand[-1]
                row_values = cand
                row_index = i + 1
                break
    if net is None:
        res.recognized = False
        res.warnings.append("Montant net introuvable dans l'avis d'opéré.")
        return res

    # Décomposition commission / TTF
    comm, ttf = 0.0, 0.0
    header_i = None
    for i, l in enumerate(lines):
        n = _norm(l)
        if n.startswith("MONTANTBRUTCOMMISSION"):        # avis domestique
            header_i = i
            nums = _nums(lines[i + 1]) if i + 1 < len(lines) else []
            # [brut, commission, (frais TTF), net] ; sans TTF : 3 nombres
            if len(nums) == 4:
                comm, ttf = nums[1], nums[2]
            elif len(nums) == 3:
                comm, ttf = nums[1], 0.0
            break
        if n.startswith("COMMISSIONFRAISDIVERS"):        # avis étranger : [commission, frais divers, total]
            nums = _nums(lines[i + 1]) if i + 1 < len(lines) else []
            if len(nums) >= 2:
                comm = nums[0] + nums[1]                # frais divers rangés avec la commission
            break

    op.commission, op.ttf = round(comm, 2), round(ttf, 2)

    # contrôle de cohérence : net = qty × cours ± frais (au centime)
    if op.quantity and op.price:
        brut = round(op.quantity * op.price + 1e-9, 2)
        frais = op.commission + op.ttf
        attendu = round(brut + frais, 2) if op_type == "ACHAT" else round(brut - frais, 2)
        if abs(attendu - net) > 0.011:
            op.notes.append(
                f"Écart de cohérence : quantité × cours ± frais = {attendu:.2f} € alors que l'avis indique {net:.2f} €. "
                "Vérifiez les champs avant d'enregistrer."
            )
    op.label = f"{op_type.title()} {op.quantity:g} × {op.name} — {op.date.strftime('%d/%m/%Y') if op.date else '?'}"
    if not (op.date and op.quantity and op.price):
        res.recognized = False
        res.warnings.append("Avis d'opéré : date, quantité ou cours introuvable.")
        return res
    res.ops.append(op)
    return res


# ----------------------------------------------------------------------------------------------
# Relevé de coupons / dividendes
# ----------------------------------------------------------------------------------------------
_COUPON_RE = re.compile(r"^(\d{2}/\d{2}/\d{4})\s+" + _QTY + r"\s+(.+?)\s*\(([A-Z]{2}[A-Z0-9]{9}\d)\)\s+(.*)$")
_REMB_RE = re.compile(r"^(\d{2}/\d{2}/\d{4})\s+(.+?)\s*\(([A-Z]{2}[A-Z0-9]{9}\d)\)\s+(.*)$")


def parse_coupons(pages) -> ParseResult:
    res = ParseResult("coupons", _DOC_LABELS["coupons"], recognized=True)
    lines = [l for p in pages for l in p["lines"]]
    section = None
    coupons, rembs = [], []
    for l in lines:
        n = _norm(l)
        if n.startswith("DETAILCOUPONS"):
            section = "coupons"
            continue
        if n.startswith("DETAILREMBOURSEMENTS"):
            section = "remb"
            continue
        if section == "coupons":
            m = _COUPON_RE.match(l)
            if m:
                nums = _nums(m.group(5))
                if len(nums) < 2:
                    continue
                coupons.append((m.group(1), _num(m.group(2)), m.group(3).strip(), m.group(4), nums))
        elif section == "remb":
            m = _REMB_RE.match(l)
            if m:
                nums = _nums(m.group(4))
                if nums:
                    rembs.append((m.group(1), m.group(2).strip(), m.group(3), nums))

    for dt, qty, name, isin, nums in coupons:
        brut, net_client = nums[0], nums[-1]
        retenue = round(brut - net_client, 2)
        op = ParsedOp(type="DIVIDENDE", date=_d(dt), name=name, isin=isin, quantity=qty,
                      amount=round(brut, 2), withholding=max(retenue, 0.0))
        if retenue < -0.005:
            op.notes.append("Net crédité supérieur au brut : vérifiez les montants.")
        if retenue > 0.005:
            op.notes.append(
                f"Retenue = brut − net crédité = {retenue:.2f} € (retenue étrangère / crédit d'impôt). Vérifiez qu'elle correspond à votre convention."
            )
        op.label = f"Dividende {name} ({qty:g} titres) — {dt}"
        res.ops.append(op)

    # Remboursements de capital : rattachés au coupon de la même valeur (même ISIN) s'il existe
    for dt, name, isin, nums in rembs:
        montant = nums[-1]
        target = next((o for o in res.ops if o.isin == isin and o.capital_repayment is None), None)
        if target:
            target.capital_repayment = round(montant, 2)
            target.notes.append(f"Inclut le remboursement de capital de {montant:.2f} € versé le {dt}.")
        else:
            op = ParsedOp(type="DIVIDENDE", date=_d(dt), name=name, isin=isin, quantity=None, amount=0.0,
                          capital_repayment=round(montant, 2))
            op.notes.append("Remboursement de capital seul (pas de coupon associé) : renseignez la quantité.")
            op.label = f"Remboursement de capital {name} — {dt}"
            res.ops.append(op)

    if not res.ops:
        res.recognized = False
        res.warnings.append("Aucune ligne de coupon trouvée dans ce relevé.")
    return res


# ----------------------------------------------------------------------------------------------
# Avis d'opération sur titres (attribution gratuite / regroupement)
# ----------------------------------------------------------------------------------------------
def parse_ost(pages) -> ParseResult:
    res = ParseResult("ost", _DOC_LABELS["ost"], recognized=True)
    lines = [l for p in pages for l in p["lines"]]
    joined = "\n".join(lines)
    n = _norm(joined)

    md = re.search(r"\bLe\s*(\d{2}/\d{2}/\d{4})", joined)
    mi = re.search(r"Code\s*Valeur\s*:\s*([A-Z]{2}[A-Z0-9]{9}\d)", joined)
    # nom de la valeur = ligne qui précède "Code Valeur"
    name = ""
    for i, l in enumerate(lines):
        if _norm(l).startswith("CODEVALEUR") and i > 0:
            name = lines[i - 1].strip()
            break

    if "ATTRIBUTIONGRATUITE" in n:
        # "1 action nouvelle X pour 10 actions anciennes"
        m = re.search(r"proportion\s*de\s*:\s*(\d+)\s*action[s]?\s*nouvelle[s]?.*?pour\s*(\d+)\s*action[s]?\s*ancienne", joined, re.S | re.I)
        if m and md:
            new, old = int(m.group(1)), int(m.group(2))
            factor = round(1 + new / old, 6)
            mq = re.search(r"Nombre\s*de\s*titres\s*:\s*(\d+)", joined)
            op = ParsedOp(type="SPLIT", date=_d(md.group(1)), name=name, isin=mi.group(1) if mi else "",
                          quantity=float(mq.group(1)) if mq else None, factor=factor)
            op.label = f"Attribution gratuite {new} pour {old} sur {name} — {md.group(1)}"
            op.notes.append(
                f"Attribution gratuite {new} nouvelle(s) pour {old} anciennes → facteur {factor:g}. "
                "Les rompus (fractions) sont indemnisés en espèces plus tard : saisissez-les via le champ « Rompu versé en cash » une fois crédités."
            )
            res.ops.append(op)
            return res

    if "REGROUPEMENT" in n or "DIVISION" in n:
        m = re.search(r"(\d+)\s*action[s]?\s*nouvelle[s]?.*?(?:pour|contre)\s*(\d+)\s*action[s]?\s*ancienne", joined, re.S | re.I)
        if m and md:
            new, old = int(m.group(1)), int(m.group(2))
            op = ParsedOp(type="SPLIT", date=_d(md.group(1)), name=name, isin=mi.group(1) if mi else "",
                          factor=round(new / old, 6))
            op.label = f"Split/Regroupement {new} pour {old} sur {name} — {md.group(1)}"
            res.ops.append(op)
            return res

    res.recognized = False
    res.warnings.append("Type d'opération sur titres non pris en charge par les règles automatiques.")
    return res


# ----------------------------------------------------------------------------------------------
# Relevé de compte espèces : uniquement les virements (apports / retraits)
# ----------------------------------------------------------------------------------------------
_ESP_LINE_RE = re.compile(r"^(\d{2}/\d{2}/\d{4})\s+(.*)$")


def _credit_header_x(words):
    """x du début de l'en-tête « Crédit ». Les montants sont alignés à droite ~10 pt plus loin que les
    en-têtes : un montant dont le bord droit dépasse ce x est dans la colonne Crédit, sinon Débit."""
    for w in words:
        if _norm(w["text"]) == "CREDIT":
            return w["x0"]
    return None


def _amount_from_right(ws):
    """Lit le montant en fin de ligne : '500,00', '1.003,39' (relevés 2026) ou '1' + '500,00' (anciens
    relevés, milliers séparés par une espace). Retourne (montant, [mots utilisés]) ou (None, [])."""
    if not ws:
        return None, []
    last = ws[-1]["text"]
    if re.fullmatch(r"\d{1,3}(?:\.\d{3})*,\d{2}|\d+,\d{2}", last):
        used = [ws[-1]]
        if len(ws) >= 2 and re.fullmatch(r"\d{3},\d{2}", last) and re.fullmatch(r"\d{1,3}", ws[-2]["text"]) \
                and 0 <= ws[-1]["x0"] - ws[-2]["x1"] < 6:
            used.insert(0, ws[-2])
        txt = " ".join(w["text"] for w in used)
        return _num(txt), used
    return None, []


def parse_releve_especes(pages) -> ParseResult:
    res = ParseResult("releve_especes", _DOC_LABELS["releve_especes"], recognized=True)
    ignored = 0
    for p in pages:
        cre_x = _credit_header_x(p["words"])
        # regrouper les mots par ligne (même "top") pour retrouver la position du montant
        rows = {}
        for w in p["words"]:
            rows.setdefault(round(w["top"] / 3), []).append(w)
        for key in sorted(rows):
            ws = sorted(rows[key], key=lambda w: w["x0"])
            line = " ".join(w["text"] for w in ws)
            m = _ESP_LINE_RE.match(line)
            if not m:
                continue
            body = m.group(2)
            nb = _norm(body)
            if nb.startswith(("ANCIENSOLDE", "NOUVEAUSOLDE", "SOLDEAU", "NOUVEAU")):
                continue
            if not nb.startswith("VIR"):
                if nb.startswith(("ACHAT", "VENTE", "COUPON", "LIQUID", "REMBOURSEMENT", "SOUSCRIPTION")):
                    ignored += 1
                continue
            # Montant = dernier nombre de la ligne, lu MOT PAR MOT depuis la droite : évite d'avaler une
            # année ("2021 400,00" ≠ 21 400) ou une date de valeur ("29/07/2026 500,00" ≠ 26 500).
            amount, amount_words = _amount_from_right(ws)
            if amount is None:
                continue
            last_w = amount_words[-1]
            sens = None
            if cre_x is not None:
                sens = "APPORT" if last_w["x1"] > cre_x else "RETRAIT"
            notes = []
            if sens is None:
                sens = "APPORT"
                notes.append("Sens (débit/crédit) non déterminé : vérifiez s'il s'agit d'un apport ou d'un retrait.")
            n_amount = len(amount_words)
            libelle_words = [w["text"] for w in ws[1:len(ws) - n_amount]]   # ws[0] = date comptable
            libelle = re.sub(r"^VIR\s*", "", " ".join(libelle_words), flags=re.I).strip()
            libelle = re.sub(r"\b\d{2}/\d{2}/\d{4}\b", "", libelle).strip()
            op = ParsedOp(type=sens, date=_d(m.group(1)), amount=amount, notes=notes)
            op.label = f"{'Apport' if sens == 'APPORT' else 'Retrait'} de {amount:.2f} € — {m.group(1)} ({libelle[:40]})"
            res.ops.append(op)
    if ignored:
        res.warnings.append(
            f"{ignored} ligne(s) d'achat/vente/coupon ignorée(s) : le relevé espèces ne donne pas le détail (commission, cours…). "
            "Utilisez l'avis d'opéré ou le relevé de coupons correspondant."
        )
    if not res.ops:
        res.recognized = False if ignored == 0 else True
        res.warnings.append("Aucun virement (apport/retrait) trouvé dans ce relevé.")
    return res


# ----------------------------------------------------------------------------------------------
# Point d'entrée déterministe
# ----------------------------------------------------------------------------------------------
def parse_document(data: bytes) -> ParseResult:
    try:
        pages = extract_pages(data)
    except Exception as e:  # PDF corrompu, protégé, image…
        return ParseResult(doc_type="illisible", doc_label="Fichier illisible", recognized=False,
                           warnings=[f"Impossible de lire le PDF : {e}"])
    text = pages_to_text(pages)
    if len(text.strip()) < 40:
        return ParseResult(doc_type="scan", doc_label="PDF sans texte (scan/image)", recognized=False,
                           warnings=["Ce PDF ne contient pas de texte exploitable (scan ou photo)."])
    kind = classify(text)
    parsers = {
        "avis_opere": parse_avis_opere,
        "coupons": parse_coupons,
        "ost": parse_ost,
        "releve_especes": parse_releve_especes,
    }
    if kind in parsers:
        try:
            res = parsers[kind](pages)
        except Exception as e:
            res = ParseResult(kind, _DOC_LABELS.get(kind, kind), recognized=False,
                              warnings=[f"Erreur d'analyse : {e}"])
        return res
    res = ParseResult(kind, _DOC_LABELS.get(kind, kind), recognized=False)
    if kind in ("releve_titres", "releve_frais"):
        res.warnings.append("Ce document ne contient pas d'opération à saisir (photographie du portefeuille / frais).")
    elif kind == "ost_realisation":
        res.warnings.append("Avis de réalisation (échange/offre) : cas particulier, à saisir manuellement.")
    else:
        res.warnings.append("Format non reconnu par les règles automatiques.")
    return res


# ----------------------------------------------------------------------------------------------
# Repli "intelligent" : autres courtiers / formats inconnus (API Anthropic)
# ----------------------------------------------------------------------------------------------
_LLM_SYSTEM = """Tu es un extracteur de données pour un suivi de portefeuille PEA/compte-titres.
On te donne le texte d'un document de courtier (avis d'exécution, relevé de dividendes, avis d'opération
sur titres, relevé de compte...). Extrais TOUTES les opérations qui doivent être saisies et réponds
UNIQUEMENT par un objet JSON (pas de markdown, pas de commentaire) de la forme :
{"operations":[{
  "type": "ACHAT|VENTE|DIVIDENDE|SPLIT|APPORT|RETRAIT",
  "date": "AAAA-MM-JJ",
  "heure": "HH:MM:SS" ou null,
  "nom": "nom de la valeur" ou null,
  "isin": "ISIN" ou null,
  "quantite": nombre ou null,
  "prix_unitaire": nombre ou null,
  "commission": nombre ou null,
  "ttf": nombre ou null,
  "montant": nombre ou null,
  "retenue_source": nombre ou null,
  "remboursement_capital": nombre ou null,
  "facteur": nombre ou null,
  "note": "remarque courte" ou null
}], "avertissements": ["..."]}
Règles :
- Montants en euros, nombres avec point décimal, jamais de chaîne.
- ACHAT/VENTE : prix_unitaire = cours d'exécution par titre ; commission = courtage/commission ;
  ttf = taxe sur les transactions financières / taxes et frais divers ; quantite = nombre de titres.
- DIVIDENDE : montant = dividende BRUT total perçu ; retenue_source = prélèvement/retenue à la source ;
  quantite = nombre de titres concernés.
- SPLIT : facteur = nouvelles actions / anciennes après opération (division par 2 => 2 ; regroupement 10
  pour 1 => 0.1 ; 1 gratuite pour 10 => 1.1).
- APPORT/RETRAIT : montant = somme versée sur / retirée du compte.
- Si une information est absente, mets null : n'invente rien.
- Ignore les lignes qui ne sont pas des opérations (soldes, en-têtes, mentions légales)."""


def _redact(text: str) -> str:
    """Retire au mieux les données personnelles avant envoi à l'API (IBAN, n° de compte, e-mail,
    téléphone, lignes de titulaire/adresse). Best-effort : ne pas s'y fier comme garantie absolue."""
    text = re.sub(r"\b[A-Z]{2}\d{2}(?:[ ]?[A-Z0-9]{4}){3,7}(?:[ ]?[A-Z0-9]{1,4})?\b", "[IBAN]", text)
    text = re.sub(r"\b\d{5}[ *]\d{5}[ *]\d{8,11}(?:[ *]\d{2})?\b", "[COMPTE]", text)
    text = re.sub(r"\b\d{9,}\b", "[NUM]", text)
    text = re.sub(r"[\w.+-]+@[\w-]+\.[\w.]+", "[EMAIL]", text)
    text = re.sub(r"(?<!\w)(?:\+33|0)[\d .]{9,14}(?!\w)", "[TEL]", text)
    kept = []
    for l in text.split("\n"):
        u = l.strip().upper()
        if re.match(r"^(MR|MME|MONSIEUR|MADAME|M\.|MLLE|TITULAIRE)\b", u):
            continue
        if re.match(r"^\d{1,3}\s*(BIS|TER)?\s*(RUE|AVENUE|AV|BD|BOULEVARD|CHEMIN|IMPASSE|ALLEE|PLACE)\b", u):
            continue
        if re.match(r"^\d{5}\s+[A-Z' -]+$", u):
            continue
        kept.append(l)
    return "\n".join(kept)


def parse_with_llm(data: bytes, api_key: str, model: str = "claude-sonnet-5-5",
                   file_name: str = "document.pdf") -> ParseResult:
    """Analyse un document inconnu avec l'API Anthropic. Envoie le TEXTE du PDF (anonymisé au mieux) ;
    si le PDF n'a pas de texte (scan), envoie le PDF lui-même (non anonymisable)."""
    res = ParseResult("ia", "Analyse intelligente (IA)", method="ia")
    try:
        import anthropic
    except ImportError:
        res.warnings.append("Le paquet `anthropic` n'est pas installé (ajoutez-le à requirements.txt).")
        return res
    if not api_key:
        res.warnings.append("Clé ANTHROPIC_API_KEY absente de st.secrets.")
        return res

    content = []
    try:
        text = pages_to_text(extract_pages(data))
    except Exception:
        text = ""
    if len(text.strip()) >= 40:
        content.append({"type": "text", "text": "Document (texte extrait, données personnelles retirées) :\n\n" + _redact(text)[:60000]})
    else:
        import base64
        content.append({"type": "document",
                        "source": {"type": "base64", "media_type": "application/pdf",
                                   "data": base64.b64encode(data).decode()}})
        content.append({"type": "text", "text": "Extrais les opérations de ce document."})
        res.warnings.append("PDF sans texte : le fichier a été envoyé tel quel à l'API (non anonymisé).")

    try:
        client = anthropic.Anthropic(api_key=api_key)
        msg = client.messages.create(model=model, max_tokens=4000, system=_LLM_SYSTEM,
                                     messages=[{"role": "user", "content": content}])
        raw = "".join(b.text for b in msg.content if getattr(b, "type", "") == "text").strip()
        raw = re.sub(r"^```(?:json)?|```$", "", raw, flags=re.M).strip()
        payload = json.loads(raw)
    except Exception as e:
        res.warnings.append(f"Échec de l'analyse IA : {e}")
        return res

    for o in payload.get("operations", []):
        try:
            typ = str(o.get("type", "")).upper()
            if typ not in OP_TYPES:
                continue
            d = datetime.strptime(o["date"], "%Y-%m-%d").date()
            heure = None
            if o.get("heure"):
                try:
                    heure = _t(o["heure"])
                except Exception:
                    heure = None
            f = lambda k: (float(o[k]) if o.get(k) is not None else None)
            op = ParsedOp(type=typ, date=d, time=heure, name=(o.get("nom") or "").strip(),
                          isin=(o.get("isin") or "").strip(), quantity=f("quantite"), price=f("prix_unitaire"),
                          commission=f("commission"), ttf=f("ttf"), amount=f("montant"),
                          withholding=f("retenue_source"), capital_repayment=f("remboursement_capital"),
                          factor=f("facteur"))
            if o.get("note"):
                op.notes.append(str(o["note"]))
            op.notes.append("Extrait par IA : vérifiez chaque champ avant d'enregistrer.")
            op.label = f"{typ.title()} {op.name or ''} — {d.strftime('%d/%m/%Y')}".replace("  ", " ")
            res.ops.append(op)
        except Exception:
            continue
    res.warnings.extend(str(w) for w in payload.get("avertissements", []) if w)
    res.recognized = bool(res.ops)
    if not res.ops:
        res.warnings.append("L'IA n'a trouvé aucune opération exploitable dans ce document.")
    return res


# ----------------------------------------------------------------------------------------------
# Rapprochement avec l'historique de l'utilisateur
# ----------------------------------------------------------------------------------------------
def match_name(broker_name: str, known_names) -> tuple[Optional[str], float]:
    """Retrouve, parmi les noms déjà présents dans l'app, celui qui correspond au libellé du courtier.
    Retourne (nom_connu, score 0-1) ou (None, score) si rien de convaincant."""
    target = _norm(broker_name)
    if not target:
        return None, 0.0
    best, best_score = None, 0.0
    for k in known_names:
        kn = _norm(k)
        if not kn:
            continue
        if kn == target:
            return k, 1.0
        score = SequenceMatcher(None, target, kn).ratio()
        if kn in target or target in kn:
            score = max(score, 0.85 if min(len(kn), len(target)) >= 4 else 0.0)
        if score > best_score:
            best, best_score = k, score
    return (best, best_score) if best_score >= 0.72 else (None, best_score)


# ----------------------------------------------------------------------------------------------
# Détection de doublons (évite de saisir deux fois la même opération)
# ----------------------------------------------------------------------------------------------
def find_duplicate(op: ParsedOp, df, known_name: Optional[str] = None) -> Optional[str]:
    """Retourne une description de l'opération déjà enregistrée qui ressemble à `op`, sinon None.
    `df` = DataFrame des transactions de l'app (colonnes Date_Heure, Type, Nom, Quantité, Prix Unitaire (€))."""
    import pandas as pd
    if df is None or len(df) == 0 or op.date is None:
        return None
    try:
        dates = pd.to_datetime(df["Date_Heure"]).dt.date
        same_type = df["Type"] == op.type
        if op.type in ("ACHAT", "VENTE"):
            if not known_name or op.quantity is None or op.price is None:
                return None
            m = (same_type & (dates == op.date) & (df["Nom"] == known_name)
                 & ((df["Quantité"] - op.quantity).abs() < 1e-6)
                 & ((df["Prix Unitaire (€)"] - op.price).abs() < 1e-3))
        elif op.type == "DIVIDENDE":
            if not known_name or op.amount is None:
                return None
            near = dates.apply(lambda d: abs((d - op.date).days) <= 7)
            m = same_type & near & (df["Nom"] == known_name) & ((df["Prix Unitaire (€)"] - op.amount).abs() < 0.02)
        elif op.type == "SPLIT":
            if not known_name:
                return None
            m = same_type & (dates == op.date) & (df["Nom"] == known_name)
        elif op.type in ("APPORT", "RETRAIT"):
            if op.amount is None:
                return None
            m = same_type & (dates == op.date) & ((df["Quantité"] - op.amount).abs() < 0.005)
        else:
            return None
        hit = df[m]
        if len(hit):
            r = hit.iloc[0]
            return f"{r['Type']} du {pd.to_datetime(r['Date_Heure']).strftime('%d/%m/%Y')}" + (f" — {r['Nom']}" if r["Nom"] else "")
    except Exception:
        return None
    return None
