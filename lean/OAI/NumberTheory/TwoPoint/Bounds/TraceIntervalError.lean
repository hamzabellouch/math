import OAI.NumberTheory.TwoPoint.Bounds.PhysicalMatrixComparison

namespace OAI

/-! The finite word-comparison error absorbs the full physical trace
catalog, including every initial vertex and both words of the pair. -/

namespace TwoPointCorrelations

lemma trace_interval_error_le_one (L : ℝ) (k : ℕ) (v e : ℝ)
    (hL : 4800 ≤ L) (hk : (k : ℝ) ≤ L) (he0 : 0 ≤ e)
    (hv : v ≤ Real.exp (106 * L)) (he : e ≤ Real.exp (L ^ 4)) :
    v * e ^ (2 * k) * Real.exp (-(L ^ 9)) ≤ 1 := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL2 : 106 ≤ L ^ 2 := by nlinarith
  have hL4 : 106 ≤ L ^ 4 := hL2.trans (pow_le_pow_right₀ hL1 (by norm_num))
  have h15 : 106 * L ≤ L ^ 5 := by
    have hh := mul_le_mul_of_nonneg_right hL4 hL0
    nlinarith
  have h59 : 3 * L ^ 5 ≤ L ^ 9 := by
    have hh := mul_le_mul_of_nonneg_right (show 3 ≤ L ^ 4 by linarith) (pow_nonneg hL0 5)
    nlinarith
  calc
    _ ≤ Real.exp (106 * L) * (Real.exp (L ^ 4)) ^ (2 * k) * Real.exp (-(L ^ 9)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hv (pow_le_pow_left₀ he0 he _) (pow_nonneg he0 _) (Real.exp_pos _).le
    _ = Real.exp (106 * L + (2 * k : ℕ) * L ^ 4 - L ^ 9) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
    _ ≤ Real.exp (106 * L + 2 * L ^ 5 - L ^ 9) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hk (pow_nonneg hL0 4)
      push_cast
      nlinarith
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

end TwoPointCorrelations

end OAI
