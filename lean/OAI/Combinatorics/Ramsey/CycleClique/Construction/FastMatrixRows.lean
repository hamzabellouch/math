import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastCertificateMatrix

namespace OAI

/-! A matrix row depends only on certificates incident with its index. -/

namespace CycleClique.Construction
def templateIncident {n : ℕ} (i : Fin n) (Tb : TemplateData (Fin n) × ℕ) : Bool :=
  decide (i = Tb.1.x ∨ i = Tb.1.y)

theorem templateMaskMatrix_filter_row {n : ℕ}
    (E : List (TemplateData (Fin n) × ℕ)) (i j : Fin n) :
    templateMaskMatrix (E.filter (templateIncident i)) i j = templateMaskMatrix E i j := by
  induction E with
  | nil => rfl
  | cons Tb E ih =>
    by_cases h : i = Tb.1.x ∨ i = Tb.1.y
    · have hh : templateIncident i Tb = true := by simp [templateIncident, h]
      simp only [List.filter_cons, hh, ite_true, templateMaskMatrix, ih]
    · have hh : templateIncident i Tb = false := by simp [templateIncident, h]
      have he : templateMaskEntry Tb.1 Tb.2 i j = 0 := by
        simp only [templateMaskEntry]
        split_ifs with he
        · exact False.elim (h (he.elim (fun hx => Or.inl hx.1) (fun hy => Or.inr hy.1)))
        · rfl
      simp only [List.filter_cons, hh, Bool.false_eq_true, ite_false, templateMaskMatrix, he,
        Nat.zero_or, ih]

def requiredIncident {n : ℕ} (i : Fin n) (p : RequiredPathData (Fin n)) : Bool :=
  decide (i = p.x ∨ i = p.y)

theorem requiredMatrix_filter_row {n : ℕ} (k : ℕ)
    (E : List (RequiredPathData (Fin n))) (i j : Fin n) :
    requiredMatrix k (E.filter (requiredIncident i)) i j = requiredMatrix k E i j := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    by_cases h : i = p.x ∨ i = p.y
    · have hh : requiredIncident i p = true := by simp [requiredIncident, h]
      simp only [List.filter_cons, hh, ite_true, requiredMatrix, ih]
    · have hh : requiredIncident i p = false := by simp [requiredIncident, h]
      have he : requiredEntryMatrix k p i j = ∅ := by
        simp only [requiredEntryMatrix]
        split_ifs with he
        · exact False.elim (h (he.elim (fun hx => Or.inl hx.1) (fun hy => Or.inr hy.1)))
        · rfl
      simp only [List.filter_cons, hh, Bool.false_eq_true, ite_false, requiredMatrix, he,
        Finset.empty_union, ih]

end CycleClique.Construction

end OAI
