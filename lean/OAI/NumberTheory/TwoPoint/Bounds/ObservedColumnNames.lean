import OAI.NumberTheory.TwoPoint.Bounds.RegularColumnNames

namespace OAI

/-! Factor canonical occurrence names through the original observed labels. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α] {n : ℕ}

noncomputable def observedColumnName (label : Fin n → α) (perfect : Finset (Fin n))
    (name : Fin n → ℕ ⊕ ℕ) (a : α) : CanonicalColumnLabel := by
  classical
  exact if h : ∃ i, label i = a then canonicalColumnName label perfect name h.choose
    else .freshImperfect 0

theorem observedColumnName_at (label : Fin n → α) (perfect : Finset (Fin n))
    (name : Fin n → ℕ ⊕ ℕ) (i : Fin n) :
    observedColumnName label perfect name (label i) = canonicalColumnName label perfect name i := by
  classical
  have h : ∃ j, label j = label i := ⟨i, rfl⟩
  simp only [observedColumnName, dite_eq_left h]
  exact canonicalColumnName_of_label_eq label perfect name h.choose_spec

theorem canonical_forest_name_at_perfect (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n) (hi : i ∈ perfect) :
    canonicalColumnName label perfect (forestPerfectName label perfect regular number) i =
      perfectColumnName (forestPerfectName label perfect regular number i) := by
  have hp := columnRepresentative_perfect label perfect i ⟨i, hi, rfl⟩
  rw [canonicalColumnName, ite_eq_left hp]
  exact congrArg perfectColumnName (forestPerfectName_of_label_eq label perfect regular number
    _ i (columnRepresentative_label label perfect i))

/-- On actual perfect regular positions, the canonical class name is the
line number produced by the shared forest. -/
theorem observed_forest_name_regular (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n)
    (hi : i ∈ perfect) (hr : label i ∈ regular) :
    observedColumnName label perfect (forestPerfectName label perfect regular number) (label i) =
      .regular (number ⟨label i, hr⟩) := by
  rw [observedColumnName_at, canonical_forest_name_at_perfect label perfect regular number i hi]
  simp only [forestPerfectName, dite_eq_left hr, perfectColumnName]

/-- Omitted perfect classes carry an occurrence index strictly below the
original column length, independent of any numerical prime value. -/
theorem observed_forest_name_omitted (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (i : Fin n)
    (hi : i ∈ perfect) (hr : label i ∉ regular) :
    observedColumnName label perfect (forestPerfectName label perfect regular number) (label i) =
      .omitted (columnRepresentative label perfect i).val := by
  rw [observedColumnName_at, canonical_forest_name_at_perfect label perfect regular number i hi]
  simp only [forestPerfectName, dite_eq_right hr, perfectColumnName]

theorem observed_forest_name_eq_iff (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ)
    (hinj : ∀ i ∈ perfect, ∀ j ∈ perfect, ∀ (hi : label i ∈ regular) (hj : label j ∈ regular),
      number ⟨label i, hi⟩ = number ⟨label j, hj⟩ → label i = label j)
    (i j : Fin n) :
    observedColumnName label perfect (forestPerfectName label perfect regular number) (label i) =
      observedColumnName label perfect (forestPerfectName label perfect regular number) (label j) ↔
        label i = label j := by
  rw [observedColumnName_at, observedColumnName_at]
  exact canonical_forest_name_eq_iff label perfect regular number hinj i j

end TwoPointCorrelations

end OAI
