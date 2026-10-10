import OAI.Analysis.KadisonKastler.GaussianStateBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Entire vector-valued Gaussian smearing -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (F : ℝ → H) (hF : Continuous F) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C)
  (r : ℝ) (hr : 0 < r)

omit [CompleteSpace H] in
include hF hbound hr in
theorem gaussianVector_integrable (z : ℂ) :
    Integrable (fun t => gaussianStateKernel r z t • F t) := by
  have hc : Continuous (gaussianStateKernel r z) := by unfold gaussianStateKernel; fun_prop
  apply ((gaussianStateKernel_integrable hr z).norm.mul_const C).mono'
    (hc.aestronglyMeasurable.smul hF.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖gaussianStateKernel r z t • F t‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

omit [CompleteSpace H] in
include hF hbound hr in
theorem gaussianVector_hasDerivAt (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ t : ℝ, gaussianStateKernel r w t • F t)
      (∫ t : ℝ, gaussianStateKernelDeriv r z t • F t) z := by
  let R := ‖z‖ + 1
  let S := Metric.ball z 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : S ∈ 𝓝 z := Metric.ball_mem_nhds z zero_lt_one
  have hnorm {w : ℂ} (hw : w ∈ S) : ‖w‖ ≤ R := by
    have hd : dist w z < 1 := hw
    have hn : ‖w‖ ≤ ‖z‖ + dist w z := by
      calc
        ‖w‖ = ‖z + (w - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ = ‖z‖ + dist w z := by rw [dist_eq_norm]
    dsimp [R]
    linarith
  let B : ℝ → ℝ := fun t =>
    (2 * r * Real.exp (2 * r * R ^ 2)) *
      ((|t| + R) * Real.exp (-(r / 2) * t ^ 2))
  have hB : Integrable (fun t => B t * C) :=
    (gaussianStateKernelDeriv_bound_integrable hr R).mul_const C
  have hm (w : ℂ) : AEStronglyMeasurable (fun t => gaussianStateKernel r w t • F t) := by
    have hc : Continuous (gaussianStateKernel r w) := by unfold gaussianStateKernel; fun_prop
    exact hc.aestronglyMeasurable.smul hF.aestronglyMeasurable
  have hmd : AEStronglyMeasurable (fun t => gaussianStateKernelDeriv r z t • F t) := by
    have hc : Continuous (gaussianStateKernelDeriv r z) := by
      unfold gaussianStateKernelDeriv gaussianStateKernel
      fun_prop
    exact hc.aestronglyMeasurable.smul hF.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ∀ w ∈ S, ‖gaussianStateKernelDeriv r w t • F t‖ ≤ B t * C := by
    filter_upwards [] with t w hw
    rw [norm_smul]
    exact mul_le_mul (gaussianStateKernelDeriv_local_bound hr hR (hnorm hw) t)
      (hbound t) (norm_nonneg _) (by dsimp [B]; positivity)
  have hd : ∀ᵐ t : ℝ, ∀ w ∈ S,
      HasDerivAt (fun w => gaussianStateKernel r w t • F t)
        (gaussianStateKernelDeriv r w t • F t) w := by
    filter_upwards [] with t w _
    exact (gaussianStateKernel_hasDerivAt r t w).smul_const (F t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall hm) (gaussianVector_integrable F hF C hbound r hr z)
    hmd hb hB hd).2

omit [CompleteSpace H] in
include hF hbound hr in
theorem gaussianVector_differentiable :
    Differentiable ℂ (fun z : ℂ => ∫ t : ℝ, gaussianStateKernel r z t • F t) :=
  fun z => (gaussianVector_hasDerivAt F hF C hbound r hr z).differentiableAt

end

end KadisonKastler

end OAI
