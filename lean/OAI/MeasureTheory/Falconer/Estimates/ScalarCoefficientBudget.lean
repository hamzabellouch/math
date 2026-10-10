import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientClosure

namespace OAI

/-! Explicit polynomial losses for finitely many scalar sum-product
operations. No generation or density assertion is assumed here. -/
namespace Falconer

def scalarCoefficientBudget (M : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => K
  | n+1 => 32768*((scalarCoefficientRadius M n : ℝ)+4)*(scalarCoefficientBudget M K n)^8

 theorem scalar_coefficient_step_bounds (r : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    let C := 32768*((r : ℝ)+4)
    L ≤ C*L^8 ∧ 19712*L^7 ≤ C*L^8 ∧
      3584*(4*r+11)*L^8 ≤ C*L^8 ∧ 8*L^2 ≤ C*L^8 := by
  dsimp only
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hC : (19712 : ℝ) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hC1 : (1 : ℝ) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hC8 : (8 : ℝ) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hCm : 3584*(4*(r : ℝ)+11) ≤ 32768*((r : ℝ)+4) := by nlinarith
  have hpow1 : L ≤ L^8 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ (8 : ℕ) by omega)
  have hpow7 := pow_le_pow_right₀ hL (show 7 ≤ (8 : ℕ) by omega)
  have hpow2 := pow_le_pow_right₀ hL (show 2 ≤ (8 : ℕ) by omega)
  refine ⟨hpow1.trans ?_,?_,?_,?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 (pow_nonneg (zero_le_one.trans hL) 8)
  · exact (mul_le_mul_of_nonneg_left hpow7 (by norm_num : (0 : ℝ) ≤ 19712)).trans
      (mul_le_mul_of_nonneg_right hC (by positivity))
  · exact mul_le_mul_of_nonneg_right hCm (by positivity)
  · exact (mul_le_mul_of_nonneg_left hpow2 (by norm_num : (0 : ℝ) ≤ 8)).trans
      (mul_le_mul_of_nonneg_right hC8 (by positivity))

 theorem scalarCoefficientBudget_one_le (M : ℕ) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    1 ≤ scalarCoefficientBudget M K n := by
  induction n with
  | zero => exact hK
  | succ n ih => exact ih.trans (scalar_coefficient_step_bounds (scalarCoefficientRadius M n) ih).1

 theorem scalarCoefficientBudget_zero_le (M : ℕ) {K : ℝ} (hK : 1 ≤ K) (n : ℕ) :
    K ≤ scalarCoefficientBudget M K n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih.trans (scalar_coefficient_step_bounds (scalarCoefficientRadius M n)
      (scalarCoefficientBudget_one_le M hK n)).1

 theorem scalarCoefficientBudget_factor (M : ℕ) (K : ℝ) (n : ℕ) :
    scalarCoefficientBudget M K n = scalarCoefficientBudget M 1 n*K^(8^n) := by
  induction n with
  | zero => simp [scalarCoefficientBudget]
  | succ n ih =>
    simp only [scalarCoefficientBudget,ih,mul_pow,← pow_mul,pow_succ]
    ring

end Falconer

end OAI
