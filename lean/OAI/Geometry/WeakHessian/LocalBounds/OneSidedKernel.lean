import Mathlib
import OAI.Geometry.WeakHessian.Entropy.SmoothDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma smoothDensity_zero_of_nonnegative_support {κ : ℝ → ℝ}
    (hc : Continuous κ) (hn : ∀ r, 0 ≤ κ r) (hi : Integrable κ)
    (hm : ∫ r, κ r = 1) (hs : ∀ r, r < 0 → κ r = 0)
    (u : Time → Lp ℝ 2 m) : smoothDensity κ u 0 = u timeZero := by
  rw [smoothDensity_eq_average hc hn,integral_kernelMeasure hc hn]
  have he : (fun r : ℝ => κ r • u (clampTime (0-r))) = fun r => κ r • u timeZero := by
    funext r
    by_cases hr : r < 0
    · simp only [hs r hr,zero_smul]
    · have hz : clampTime (0-r) = timeZero := by
        apply Subtype.ext
        simp only [clampTime,timeZero]
        apply max_eq_left
        exact min_le_of_right_le (by linarith)
      rw [hz]
  rw [he]
  calc
    _ = (∫ r, κ r) • u timeZero :=
      ((1 : ℝ →L[ℝ] ℝ).smulRight (u timeZero)).integral_comp_comm hi
    _ = u timeZero := by rw [hm, one_smul]

end WeakHessian

end
end

end OAI
