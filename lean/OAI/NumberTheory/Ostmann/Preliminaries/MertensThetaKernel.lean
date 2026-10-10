import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionPrincipalPNT

namespace OAI

/-! # Integrating the conductor-one theta error

The exponential square-root error has a bounded logarithmic integral. This
concrete antiderivative suffices for the first Mertens estimate.
-/

namespace Ostmann

open MeasureTheory
open scoped Interval

noncomputable def thetaErrorPrimitive (c t : ℝ) : ℝ :=
  -(2 / c ^ 2) * (c * Real.sqrt (Real.log t) + 1) *
    Real.exp (-c * Real.sqrt (Real.log t))

theorem hasDerivAt_thetaErrorPrimitive {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (thetaErrorPrimitive c)
      (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have hs := (Real.hasDerivAt_sqrt hlog.ne').comp t (Real.hasDerivAt_log ht0)
  have hl := ((hs.const_mul c).add_const 1).const_mul (-(2 / c ^ 2))
  have hr := (hs.const_mul (-c)).exp
  convert hl.mul hr using 1
  · rfl
  · simp only [Function.comp_apply]
    field_simp
    ring

theorem thetaErrorPrimitive_nonpos {c : ℝ} (hc : 0 < c) (t : ℝ) :
    thetaErrorPrimitive c t ≤ 0 := by
  unfold thetaErrorPrimitive
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
    (Real.exp_nonneg _)

/-- A uniform bound independent of the upper cutoff. -/
theorem theta_error_kernel_integral_bound {c X : ℝ} (hc : 0 < c) (hX : 2 ≤ X) :
    (∫ t in (2 : ℝ)..X, Real.exp (-c * Real.sqrt (Real.log t)) / t) ≤
      -thetaErrorPrimitive c 2 := by
  have hi : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-c * Real.sqrt (Real.log t)) / t) volume 2 X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX]
    apply ContinuousOn.integrableOn_Icc
    fun_prop (disch := grind)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
    hasDerivAt_thetaErrorPrimitive hc (by
      rw [Set.uIcc_of_le hX] at ht
      linarith [ht.1])) hi]
  linarith [thetaErrorPrimitive_nonpos hc X]

end Ostmann

end OAI
