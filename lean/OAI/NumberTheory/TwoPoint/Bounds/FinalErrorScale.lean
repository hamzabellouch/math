import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeParameterChoice

namespace OAI

/-! The residual rare-site and summed block-boundary errors are below
the same exp(-J) saving as the principal terms. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_rare_error_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, Real.exp (-L ^ (9 / 10 : ℝ)) ≤
      Real.exp (-(primeSupplyCount W L : ℝ)) := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs] with L hL hs
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < L) _), one_mul] at hs
  apply Real.exp_le_exp.mpr
  have hj := primeSupplyCount_le_log W L hW hL
  linarith

lemma eventually_bin_error_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      (L / Real.exp (-(primeSupplyCount W L : ℝ))) * Real.exp (-L) ≤
        Real.exp (-(primeSupplyCount W L : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_sublinear_log_cost 0 3 (by norm_num) (by norm_num)] with L hL hs
  simp only [Real.rpow_zero, mul_one] at hs
  have hLp : 0 < L := by linarith
  have hj := primeSupplyCount_le_log W L hW hL
  have he : L / Real.exp (-(primeSupplyCount W L : ℝ)) =
      Real.exp (Real.log L + (primeSupplyCount W L : ℝ)) := by
    rw [Real.exp_add, Real.exp_log hLp, Real.exp_neg, div_inv_eq_mul]
  rw [he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TwoPointCorrelations

end OAI
