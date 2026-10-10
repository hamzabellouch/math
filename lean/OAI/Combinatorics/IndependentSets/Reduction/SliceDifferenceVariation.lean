import Mathlib

namespace OAI

namespace LargeIndependentSets.CubeGradient
open MeasureTheory Set
open scoped NNReal

theorem slice_difference_le_variation {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) {a b x y : ℝ}
    (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    |f y - f x| ≤ ∫ t in a..b, |deriv f t| := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  have hxyac : AbsolutelyContinuousOnInterval f x y :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  rw [← hxyac.integral_deriv_eq_sub]
  exact (intervalIntegral.abs_integral_le_integral_abs hxy).trans
    (intervalIntegral.integral_mono_interval hax hxy hyb
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) hac.intervalIntegrable_deriv.abs)

theorem bit_block_variation {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in a..a+h, |f (t+h) - f t|) ≤
      h * ∫ t in a..a+2*h, |deriv f t| := by
  have hfc := hf.continuous
  have hc : Continuous (fun t => |f (t+h) - f t|) := by fun_prop
  have hle : (∫ t in a..a+h, |f (t+h) - f t|) ≤
      ∫ _t in a..a+h, ∫ u in a..a+2*h, |deriv f u| := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro t ht
    exact slice_difference_le_variation hf ht.1 (by linarith) (by linarith [ht.2])
  convert hle using 1
  simp [intervalIntegral.integral_const, smul_eq_mul]

end LargeIndependentSets.CubeGradient

end OAI
