import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalGradientBounds

namespace OAI

/-!
# An integrable dominator for fractional gradients

Schwartz derivative seminorms control the near and far parts separately, with
inverse-distance powers `p` and `p + 2`. In dimension `p + 1` their sum is
integrable and uniformly bounds the dilated gradient kernel for dilation
parameters between one half and two.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def fractionalGradientDominator {d : ℕ} (p : ℕ) (g : 𝓢(Ambient d, F))
    (x h : Ambient d) : ℝ :=
  (4 * SchwartzMap.seminorm ℝ 0 0
    (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g))) *
      (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h +
  (4 * (SchwartzMap.seminorm ℝ 1 0 (fderivCLM ℝ (Ambient d) F g) +
    ‖x‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) F g))) *
      (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h

theorem fractionalGradientDominator_integrable (p : ℕ)
    (g : 𝓢(Ambient (p + 1), F)) (x : Ambient (p + 1)) :
    Integrable (fractionalGradientDominator p g x) volume := by
  have hn := (inverseDistancePow_near_integrable_and_bound (d := p + 1) p _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  have hf := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 1 (by norm_num)).1
  exact ((hn.integrable_indicator measurableSet_closedBall).const_mul _).add
    ((hf.integrable_indicator (closedExterior_measurable 0 1)).const_mul _)

theorem dilatedFractionalGradientKernel_le_dominator {d : ℕ} (p : ℕ)
    (g : 𝓢(Ambient d, F)) (x h : Ambient d) (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) 2) :
    ‖dilatedFractionalGradientKernel (p + 1) g x t h‖ ≤ fractionalGradientDominator p g x h := by
  have htpos : 0 ≤ t := by linarith [ht.1]
  have htAbs : |t| ≤ 2 := by rw [abs_of_nonneg htpos]; exact ht.2
  have hn : 0 ≤ (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg p 0 y) h
  have hf : 0 ≤ (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h :=
    indicator_nonneg (fun y _ => inverseDistancePow_nonneg (p + 2) 0 y) h
  by_cases hh : ‖h‖ ≤ 1
  · have hmem : h ∈ closedBall (0 : Ambient d) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using! hh
    unfold fractionalGradientDominator
    rw [indicator_of_mem hmem]
    apply (schwartz_dilated_fractional_gradient_near_bound p g x h t htAbs).trans
    apply le_add_of_nonneg_right
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (apply_nonneg _ _) (mul_nonneg (norm_nonneg _) (apply_nonneg _ _)))) hf
  · have hmem : h ∈ closedExterior (0 : Ambient d) 1 := by
      simpa only [closedExterior, mem_ofPred_eq, dist_zero_left] using! (lt_of_not_ge hh).le
    unfold fractionalGradientDominator
    rw [indicator_of_mem hmem]
    apply (schwartz_dilated_fractional_gradient_far_bound (p + 1) g x h t ht.1).trans
    apply le_add_of_nonneg_left
    exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _)) hn

end

end RieszRectifiability

end OAI
