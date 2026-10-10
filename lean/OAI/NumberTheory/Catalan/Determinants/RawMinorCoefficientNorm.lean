import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Catalan.Estimates.TwoAdicSelectorExponent
import OAI.NumberTheory.Catalan.Polynomial.RawCoefficientEntryBound

namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem rawCoefficientTerm_eq_det (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) :
    (∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
        rawCoefficientMinor N c τ u =
      Matrix.det (Matrix.of fun r k : Fin (n N) =>
        rawCoefficientVector N r.val (c k).val (τ k) (u k).val *
          rawCoefficientScalar z N (c k).val (τ k) (u k).val) := by
  classical
  simp only [rawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.prod_mul_distrib]
  ring

private theorem prod_two_zpow_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    (∏ k, (2 : ℝ) ^ (-v k)) = (2 : ℝ) ^ (-(∑ k, v k)) := by
  classical
  calc
    _ = ∏ k, (2 : ℝ) ^ (((-v k) : ℤ) : ℝ) := by
      simp only [Real.rpow_intCast]
    _ = (2 : ℝ) ^ (∑ k, (((-v k) : ℤ) : ℝ)) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = (2 : ℝ) ^ (((-(∑ k, v k)) : ℤ) : ℝ) := by
      simp only [Int.cast_neg, Int.cast_sum, Finset.sum_neg_distrib]
    _ = _ := Real.rpow_intCast _ _

theorem rawCoefficientTerm_norm_le_zpow (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) :
    ‖(∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
        rawCoefficientMinor N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ (-(∑ k : Fin (n N),
          if τ k = 0 then (Cdegree N : ℤ)
          else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (H N : ℤ)
          else ((u k).val : ℤ))) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawCoefficientTerm_eq_det]
  calc
    _ ≤ ∏ k : Fin (n N),
        (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) *
          (2 : ℝ) ^ (-(if τ k = 0 then (Cdegree N : ℤ)
            else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (H N : ℤ)
            else ((u k).val : ℤ))) := by
      apply padic_two_det_norm_le_prod_column
      · intro k
        positivity
      · intro r k
        exact rawCoefficientEntry_norm_le z hN
          (Finset.mem_Ico.mp (c k).property).2 (τ k) (u k)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, prod_two_zpow_neg]

theorem rawCoefficientTerm_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) (hc : Function.Injective c)
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) :
    ‖(∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
        rawCoefficientMinor N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  have hF := discrepancyNormFactor_nonneg z
  by_cases hz : rawCoefficientMinor N c τ u = 0
  · rw [hz, mul_zero, norm_zero]
    positivity
  have hj : Function.Injective (fun k => (c k).val) := by
    intro i j hij
    exact hc (Subtype.ext hij)
  have hp := twoAdic_selector_zpow_le N τ (fun k => (u k).val) (fun k => (c k).val)
    (rawCoefficientMinor_exception_injOn N c τ u hz)
    (rawCoefficientMinor_boundary_injOn N c τ u hz) hj
    (fun k => (Finset.mem_Ico.mp (c k).property).1)
  exact (rawCoefficientTerm_norm_le_zpow z hN c τ u).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

theorem rawColumnMinor_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) (hc : Function.Injective c)
    (τ : Fin (n N) → Fin 3) :
    ‖Matrix.det (Matrix.of fun r k : Fin (n N) =>
      rawColumnTerm z N r.val (c k).val (τ k))‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawColumnMinor_coefficient_expansion]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro u hu
  exact rawCoefficientTerm_norm_le z hN c hc τ u

theorem rawMinorRat_two_adic_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N))) (hc : Function.Injective c) :
    ‖(rawMinorRat z N c : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [rawMinorRat_two_adic_column_expansion z hN c]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro τ hτ
  exact rawColumnMinor_norm_le z hN c hc τ

theorem determinantRat_two_adic_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N) :
    ‖(determinantRat z N : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ)) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [determinantRat_eq_sum_raw_minors]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro c hc
  rw [norm_mul]
  calc
    _ ≤ 1 * ((8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) ^ n N *
        (2 : ℝ) ^ ((505 / 4608 : ℝ) * (n N : ℝ) ^ 2 + 2 * (n N : ℝ))) :=
      mul_le_mul (Padic.norm_int_le_one _)
        (rawMinorRat_two_adic_norm_le z hN c (Finset.mem_filter.mp hc).2)
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

end InternalCatalan

end

end OAI
