import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalGradientDomination

namespace OAI

/-!
# Differentiating dilated fractional kernels

Measurability and the gradient dominator justify differentiation under the
integral near dilation one. Comparing with the dilation scaling identity
identifies the integrated gradient kernel with the fractional Schwartz kernel,
and hence gives the gradient representation of the fractional test.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dilatedFractionalKernel_aestronglyMeasurable {d : ℕ} (m : ℕ)
    (g : 𝓢(Ambient d, F)) (μ : Measure (Ambient d)) (x : Ambient d) (t : ℝ) :
    AEStronglyMeasurable (dilatedFractionalKernel m g x t) μ := by
  have hc : Continuous (fun h : Ambient d => symmetricSecondDifference g x (t • h)) := by
    unfold symmetricSecondDifference
    fun_prop
  exact (inverseDistancePow_measurable (m + 1) (0 : Ambient d)).aestronglyMeasurable.smul
    hc.aestronglyMeasurable

theorem dilatedFractionalGradientKernel_aestronglyMeasurable {d : ℕ} (m : ℕ)
    (g : 𝓢(Ambient d, F)) (μ : Measure (Ambient d)) (x : Ambient d) (t : ℝ) :
    AEStronglyMeasurable (dilatedFractionalGradientKernel m g x t) μ := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have hD : Continuous (fderiv ℝ (g : Ambient d → F)) :=
    (g.smooth ⊤).continuous_fderiv (by simp)
  have hp : Continuous (fun h : Ambient d => fderiv ℝ g (x + t • h) h) :=
    (hD.comp ((continuous_const (y := x)).add ((continuous_const (y := t)).smul continuous_id))).clm_apply continuous_id
  have hm : Continuous (fun h : Ambient d => fderiv ℝ g (x - t • h) h) :=
    (hD.comp ((continuous_const (y := x)).sub ((continuous_const (y := t)).smul continuous_id))).clm_apply continuous_id
  exact (inverseDistancePow_measurable (m + 1) (0 : Ambient d)).aestronglyMeasurable.smul
    (hp.sub hm).aestronglyMeasurable

theorem fractional_gradient_integral_identity [CompleteSpace F] (p : ℕ)
    (g : 𝓢(Ambient (p + 1), F)) (x : Ambient (p + 1)) :
    Integrable (dilatedFractionalGradientKernel (p + 1) g x 1) volume ∧
      (∫ h, dilatedFractionalGradientKernel (p + 1) g x 1 h) =
        ∫ h, fractionalSchwartzKernel (p + 1) g x h := by
  have hI : Integrable (dilatedFractionalKernel (p + 1) g x 1) volume := by
    have heq : dilatedFractionalKernel (p + 1) g x 1 =
        fractionalSchwartzKernel (p + 1) g x := by
      funext h
      simp only [dilatedFractionalKernel, one_smul, fractionalSchwartzKernel]
    rw [heq]
    exact fractionalSchwartzKernel_integrable_of_growth p _ volume
      (volume_global_upper_growth (p + 1)) g x
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t h => dilatedFractionalKernel (p + 1) g x t h)
    (F' := fun t h => dilatedFractionalGradientKernel (p + 1) g x t h)
    (μ := (volume : Measure (Ambient (p + 1))))
    (show Icc (1 / 2 : ℝ) 2 ∈ 𝓝 (1 : ℝ) from Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => dilatedFractionalKernel_aestronglyMeasurable (p + 1) g volume x t)
    hI (dilatedFractionalGradientKernel_aestronglyMeasurable (p + 1) g volume x 1)
    (Eventually.of_forall fun h t ht => dilatedFractionalGradientKernel_le_dominator p g x h t ht)
    (fractionalGradientDominator_integrable p g x)
    (Eventually.of_forall fun h t _ => dilatedFractionalKernel_hasDerivAt (p + 1) g g.differentiable x h t)
  have hscale : (fun t : ℝ => ∫ h, dilatedFractionalKernel (p + 1) g x t h) =ᶠ[𝓝 (1 : ℝ)]
      (fun t => t • ∫ h, fractionalSchwartzKernel (p + 1) g x h) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact dilatedFractionalKernel_integral_scaling (p + 1) g x t ht
  have hlinear : HasDerivAt (fun t : ℝ => t • ∫ h, fractionalSchwartzKernel (p + 1) g x h)
      (∫ h, fractionalSchwartzKernel (p + 1) g x h) 1 := by
    simpa only [one_smul] using! (hasDerivAt_id (1 : ℝ)).smul_const
      (∫ h, fractionalSchwartzKernel (p + 1) g x h)
  exact ⟨hparam.1, hparam.2.unique (hlinear.congr_of_eventuallyEq hscale)⟩

theorem fractionalSchwartzTest_eq_gradient_integral (p : ℕ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    fractionalSchwartzTest p g x = (-1 / 2 : ℝ) •
      ∫ h, dilatedFractionalGradientKernel (p + 1) g x 1 h := by
  rw [fractionalSchwartzTest, (fractional_gradient_integral_identity p g x).2]

end

end RieszRectifiability

end OAI
