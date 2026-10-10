import OAI.NumberTheory.TwoPoint.Bounds.MatrixAction

namespace OAI

/-! Deterministic testing of a weighted matrix. Only rows on the support
of the test vector enter the estimate. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma weighted_matrix_test_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℂ) (g R : V → ℝ) (hg : ∀ i, 0 < g i)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g i)
    (hrow : ∀ i, v i ≠ 0 → ∑ j, ‖A i j‖ * g j / g i ≤ R i) :
    ‖inner ℂ v (matrixOperator A v)‖ ≤
      ∑ i, if v i = 0 then 0 else R i * (g i) ^ 2 := by
  rw [PiLp.inner_apply]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  by_cases hi : v i = 0
  · simp [hi]
  · rw [ite_eq_right hi]
    calc
      ‖inner ℂ (v i) (matrixOperator A v i)‖ ≤ ‖v i‖ * ‖matrixOperator A v i‖ :=
        norm_inner_le_norm _ _
      _ ≤ g i * (∑ j, ‖A i j‖ * g j) := by
        apply mul_le_mul (hv i) _ (norm_nonneg _) (hg i).le
        rw [matrixOperator_apply]
        apply (norm_sum_le _ _).trans
        exact sum_le_sum (fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _))
      _ = (∑ j, ‖A i j‖ * g j / g i) * (g i) ^ 2 := by
        rw [← sum_div]
        field_simp [(hg i).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)

lemma weighted_matrix_test_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℂ) (g : V → ℝ) (R G : ℝ)
    (hg : ∀ i, 0 < g i) (hR : 0 ≤ R) (hGnonneg : 0 ≤ G)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g i)
    (hrow : ∀ i, v i ≠ 0 → ∑ j, ‖A i j‖ * g j / g i ≤ R)
    (hG : ∀ i, v i ≠ 0 → (g i) ^ 2 ≤ G) :
    ‖inner ℂ v (matrixOperator A v)‖ ≤ Fintype.card V * R * G := by
  apply (weighted_matrix_test_le A g (fun _ => R) hg v hv hrow).trans
  calc
    (∑ i, if v i = 0 then 0 else R * (g i) ^ 2) ≤ ∑ _i : V, R * G := by
      apply sum_le_sum
      intro i _
      by_cases hi : v i = 0
      · rw [ite_eq_left hi]
        exact mul_nonneg hR hGnonneg
      · rw [ite_eq_right hi]
        exact mul_le_mul_of_nonneg_left (hG i hi) hR
    _ = _ := by simp; ring

end TwoPointCorrelations

end OAI
