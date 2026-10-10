import OAI.NumberTheory.TwoPoint.Walks.CanonicalColumnNames

namespace OAI

/-! Name regular perfect classes by forest vertices and omitted classes by occurrences. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- Omitted classes use bounded occurrence indices. Regular classes use
exactly the line-vertex numbers shared across the path family. -/
def forestPerfectName (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n) : ℕ ⊕ ℕ :=
  if hi : label i ∈ regular then .inl (number ⟨label i, hi⟩)
  else .inr (columnRepresentative label perfect i).val

theorem forestPerfectName_of_label_eq (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i j : Fin n) (h : label i = label j) :
    forestPerfectName label perfect regular number i = forestPerfectName label perfect regular number j := by
  by_cases hi : label i ∈ regular <;> by_cases hj : label j ∈ regular
  · have he : (⟨label i, hi⟩ : regular) = ⟨label j, hj⟩ := Subtype.ext h
    simp only [forestPerfectName, dite_eq_left hi, dite_eq_left hj, he]
  · exact (hj (h ▸ hi)).elim
  · exact (hi (h.symm ▸ hj)).elim
  · simp only [forestPerfectName, dite_eq_right hi, dite_eq_right hj,
      (columnRepresentative_eq_iff label perfect i j).mpr h]

/-- Injectivity is needed only for lines observed at perfect positions.
No numbering requirement is imposed on unused regular labels. -/
theorem forestPerfectName_eq_iff (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ)
    (hinj : ∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j)
    (i : Fin n) (hi : i ∈ perfect) (j : Fin n) (hj : j ∈ perfect) :
    forestPerfectName label perfect regular number i = forestPerfectName label perfect regular number j ↔
      label i = label j := by
  constructor
  · intro heq
    by_cases hir : label i ∈ regular <;> by_cases hjr : label j ∈ regular
    · simp only [forestPerfectName, dite_eq_left hir, dite_eq_left hjr, Sum.inl.injEq] at heq
      exact hinj i hi j hj hir hjr heq
    · simp only [forestPerfectName, dite_eq_left hir, dite_eq_right hjr, Sum.inl_ne_inr] at heq
    · simp only [forestPerfectName, dite_eq_right hir, dite_eq_left hjr, Sum.inr_ne_inl] at heq
    · simp only [forestPerfectName, dite_eq_right hir, dite_eq_right hjr, Sum.inr.injEq] at heq
      exact (columnRepresentative_eq_iff label perfect i j).mp (Fin.ext heq)
  · exact forestPerfectName_of_label_eq label perfect regular number i j

/-- The completed names represent the full equality pattern, including
classes having no perfect occurrence. -/
theorem canonical_forest_name_eq_iff (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ)
    (hinj : ∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j)
    (i j : Fin n) :
    canonicalColumnName label perfect (forestPerfectName label perfect regular number) i =
      canonicalColumnName label perfect (forestPerfectName label perfect regular number) j ↔ label i = label j := by
  apply canonicalColumnName_eq_iff
  exact forestPerfectName_eq_iff label perfect regular number hinj

end TwoPointCorrelations

end OAI
