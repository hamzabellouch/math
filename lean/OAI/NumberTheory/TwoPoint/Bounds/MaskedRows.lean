import OAI.NumberTheory.TwoPoint.Bounds.WeightedRows

namespace OAI

/-! Edge deletions preserve the weighted-row estimates. -/

namespace TwoPointCorrelations

open Finset

variable {ι : Type*} [Fintype ι]

noncomputable def maskMatrix (gate : ι → ι → Prop) (A : ι → ι → ℂ) (i j : ι) : ℂ := by
  classical
  exact if gate i j then A i j else 0

omit [Fintype ι] in
lemma maskMatrix_norm_le (gate : ι → ι → Prop) (A : ι → ι → ℂ) (i j : ι) :
    ‖maskMatrix gate A i j‖ ≤ ‖A i j‖ := by
  classical
  unfold maskMatrix
  split_ifs
  · exact le_rfl
  · simp

omit [Fintype ι] in
lemma maskMatrix_norm_symmetric (gate : ι → ι → Prop) (A : ι → ι → ℂ)
    (hgate : ∀ i j, gate i j ↔ gate j i)
    (hA : ∀ i j, ‖A i j‖ = ‖A j i‖) (i j : ι) :
    ‖maskMatrix gate A i j‖ = ‖maskMatrix gate A j i‖ := by
  classical
  simp only [maskMatrix, hgate i j]
  split_ifs
  · exact hA i j
  · rfl

omit [Fintype ι] in
lemma maskMatrix_level (gate : ι → ι → Prop) (A : ι → ι → ℂ) (a : ι → ℝ)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j) (i j : ι)
    (hij : maskMatrix gate A i j ≠ 0) : a i = a j := by
  classical
  apply hlevel i j
  intro hz
  exact hij (by simp [maskMatrix, hz])

lemma maskMatrix_weighted_row (gate : ι → ι → Prop) (A : ι → ι → ℂ)
    (g a : ι → ℝ) (c : ℝ) (hg : ∀ i, 0 < g i)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ c * a i) (i : ι) :
    ∑ j, ‖maskMatrix gate A i j‖ * g j / g i ≤ c * a i := by
  apply le_trans _ (hrow i)
  apply sum_le_sum
  intro j _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (maskMatrix_norm_le gate A i j) (hg j).le) (hg i).le

end TwoPointCorrelations

end OAI
