import OAI.Combinatorics.Ramsey.CycleClique.Construction.TemplateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RequiredCertificates
import Mathlib.Data.Nat.Bitwise

namespace OAI

/-! Natural-number masks provide a compact, checked representation of
finite forbidden matrices. The supplied masks are validated separately. -/

namespace CycleClique.Construction
/-- Decode the first `w` bits of a natural-number mask. -/
def decode (w b : ℕ) : Finset ℕ :=
  (Finset.range w).filter (fun d => Nat.testBit b d)

@[simp] theorem decode_zero (w : ℕ) : decode w 0 = ∅ := by
  simp [decode]

theorem decode_or (w b c : ℕ) : decode w (b ||| c) = decode w b ∪ decode w c := by
  ext d
  simp [decode, Nat.testBit_or, and_or_left]

def templateMaskEntry {n : ℕ} (T : TemplateData (Fin n)) (b : ℕ) :
    Fin n → Fin n → ℕ := fun i j =>
  if (i = T.x ∧ j = T.y) ∨ (i = T.y ∧ j = T.x) then b else 0

def templateMaskMatrix {n : ℕ} :
    List (TemplateData (Fin n) × ℕ) → Fin n → Fin n → ℕ
  | [] => fun _ _ => 0
  | Tb :: E => fun i j => templateMaskEntry Tb.1 Tb.2 i j ||| templateMaskMatrix E i j

theorem templateMaskMatrix_append {n : ℕ}
    (A B : List (TemplateData (Fin n) × ℕ)) :
    templateMaskMatrix (A ++ B) =
      fun i j => templateMaskMatrix A i j ||| templateMaskMatrix B i j := by
  induction A with
  | nil =>
    funext i j
    simp only [List.nil_append, templateMaskMatrix, Nat.zero_or]
  | cons Tb A ih =>
    funext i j
    simp only [List.cons_append, templateMaskMatrix, ih, Nat.or_assoc]

theorem decode_templateMaskEntry {n w b : ℕ} {T : TemplateData (Fin n)}
    (hdecode : decode w b = Finset.Icc T.lo T.hi) (i j : Fin n) :
    decode w (templateMaskEntry T b i j) = templateEntryMatrix T i j := by
  unfold templateMaskEntry templateEntryMatrix
  split_ifs
  · exact hdecode
  · exact decode_zero w

theorem decode_templateMaskMatrix {n : ℕ} (w : ℕ)
    (E : List (TemplateData (Fin n) × ℕ))
    (hE : ∀ Tb ∈ E, decode w Tb.2 = Finset.Icc Tb.1.lo Tb.1.hi) :
    (fun i j => decode w (templateMaskMatrix E i j)) = templateMatrix (E.map Prod.fst) := by
  induction E with
  | nil =>
    funext i j
    exact decode_zero w
  | cons Tb E ih =>
    have hT := hE Tb (by simp)
    have htail := ih (fun Tc hTc => hE Tc (by simp [hTc]))
    funext i j
    change decode w (templateMaskEntry Tb.1 Tb.2 i j ||| templateMaskMatrix E i j) =
      templateEntryMatrix Tb.1 i j ∪ templateMatrix (E.map Prod.fst) i j
    rw [decode_or, decode_templateMaskEntry hT, congrFun (congrFun htail i) j]

def requiredMaskEntry {n : ℕ} (p : RequiredPathData (Fin n)) (b : ℕ) :
    Fin n → Fin n → ℕ := fun i j =>
  if (i = p.x ∧ j = p.y) ∨ (i = p.y ∧ j = p.x) then b else 0

def requiredMaskMatrix {n : ℕ} :
    List (RequiredPathData (Fin n) × ℕ) → Fin n → Fin n → ℕ
  | [] => fun _ _ => 0
  | pb :: E => fun i j => requiredMaskEntry pb.1 pb.2 i j ||| requiredMaskMatrix E i j

theorem requiredMaskMatrix_append {n : ℕ}
    (A B : List (RequiredPathData (Fin n) × ℕ)) :
    requiredMaskMatrix (A ++ B) =
      fun i j => requiredMaskMatrix A i j ||| requiredMaskMatrix B i j := by
  induction A with
  | nil =>
    funext i j
    simp only [List.nil_append, requiredMaskMatrix, Nat.zero_or]
  | cons pb A ih =>
    funext i j
    simp only [List.cons_append, requiredMaskMatrix, ih, Nat.or_assoc]

theorem decode_requiredMaskEntry {n w b : ℕ} (k : ℕ) {p : RequiredPathData (Fin n)}
    (hdecode : decode w b = {p.parameter k}) (i j : Fin n) :
    decode w (requiredMaskEntry p b i j) = requiredEntryMatrix k p i j := by
  unfold requiredMaskEntry requiredEntryMatrix
  split_ifs
  · exact hdecode
  · exact decode_zero w

theorem decode_requiredMaskMatrix {n : ℕ} (w k : ℕ)
    (E : List (RequiredPathData (Fin n) × ℕ))
    (hE : ∀ pb ∈ E, decode w pb.2 = {pb.1.parameter k}) :
    (fun i j => decode w (requiredMaskMatrix E i j)) = requiredMatrix k (E.map Prod.fst) := by
  induction E with
  | nil =>
    funext i j
    exact decode_zero w
  | cons pb E ih =>
    have hp := hE pb (by simp)
    have htail := ih (fun pc hpc => hE pc (by simp [hpc]))
    funext i j
    change decode w (requiredMaskEntry pb.1 pb.2 i j ||| requiredMaskMatrix E i j) =
      requiredEntryMatrix k pb.1 i j ∪ requiredMatrix k (E.map Prod.fst) i j
    rw [decode_or, decode_requiredMaskEntry k hp, congrFun (congrFun htail i) j]

end CycleClique.Construction

end OAI
