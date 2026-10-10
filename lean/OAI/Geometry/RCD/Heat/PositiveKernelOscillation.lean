import OAI.Geometry.RCD.Heat.PositiveKernelLogDerivative
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Strict oscillation contraction of the positive kernel transform

The estimate compares two rows with one common exponent. Integrating
the derivative along the line joining two exponents is the scalar step
in the heat-kernel scaling construction.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

theorem positiveKernelLogTilt_oscillation {k v r d : Y → ℝ} {m M a b : ℝ}
    (hr : Integrable r μ) (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hmass : 0 < ∫ x, r x ∂μ) (hk : Measurable k) (hv : Measurable v)
    (hd : Measurable d) (hm : 0 < m)
    (hkb : ∀ x, m ≤ k x ∧ k x ≤ M) (hvb : ∀ x, m ≤ v x ∧ v x ≤ M)
    {D : ℝ≥0} (hdb : ∀ x, |d x| ≤ D)
    (hab : ∀ᵐ x ∂μ, a ≤ d x ∧ d x ≤ b) :
    |(positiveKernelLogTilt μ k r d 1 - positiveKernelLogTilt μ v r d 1) -
      (positiveKernelLogTilt μ k r d 0 - positiveKernelLogTilt μ v r d 0)| ≤
        (1-m/M)*(b-a) := by
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt
        (fun s => positiveKernelLogTilt μ k r d s - positiveKernelLogTilt μ v r d s)
        (positiveKernelLogTiltDerivative μ k r d t -
          positiveKernelLogTiltDerivative μ v r d t) (Icc 0 1) t := by
    intro t _
    exact ((positiveKernelLogTilt_hasDerivAt μ hr hr0 hmass hk hd hm hkb hdb t).sub
      (positiveKernelLogTilt_hasDerivAt μ hr hr0 hmass hv hd hm hvb hdb t)).hasDerivWithinAt
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖positiveKernelLogTiltDerivative μ k r d t -
        positiveKernelLogTiltDerivative μ v r d t‖ ≤ (1-m/M)*(b-a) := by
    intro t _
    exact positiveKernelLogTiltDerivative_difference μ hr hr0 hmass hk hv hd hm hkb hvb hdb hab t
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc 0 1)
    (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp)
  simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using h

end RegularPointCoordinates

end

end OAI
