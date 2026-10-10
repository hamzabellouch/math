import OAI.Probability.MatroidProphet.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace MatroidProphet

noncomputable def residualDelta : ℝ := ((2 : ℝ)^26)⁻¹

lemma residual_tail_coefficient :
    (1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2) *
      densityThreshold ≤ -(26 * Real.log 2) := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold densityThreshold residualDelta
  rw [Real.log_pow]
  norm_num
  nlinarith

theorem residual_tail_constant (n : ℝ) (hn : densityThreshold ≤ n) :
    Real.exp ((1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2) * n)
      ≤ residualDelta := by
  have hk : 0 < densityThreshold := constants_positive.2.1
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hc := residual_tail_coefficient
  have hneg : 1000 * Real.log densityThreshold / densityThreshold - residualDelta * Real.log 2 ≤ 0 := by
    nlinarith
  have hmul := mul_le_mul_of_nonpos_left hn hneg
  have he := Real.exp_le_exp.mpr (hmul.trans hc)
  have hid : Real.exp (-(26 * Real.log (2 : ℝ))) = residualDelta := by
    rw [Real.exp_neg]
    have hpow := Real.exp_nat_mul (Real.log (2 : ℝ)) 26
    norm_num at hpow
    rw [hpow]
    rw [Real.exp_log (by norm_num)]
    rfl
  rwa [hid] at he

theorem residual_error_constant : densityThreshold⁻¹ + 2 * residualDelta ≤ ((2 : ℝ)^23)⁻¹ := by
  norm_num [densityThreshold, residualDelta]

end MatroidProphet

end OAI
