import Mathlib
import OAI.Probability.SKSupport.Diffusion.AbsIncrement
import OAI.Probability.SKSupport.Diffusion.FeedbackVerification
import OAI.Probability.SKSupport.Backward.BackwardGradientMild
import OAI.Probability.SKSupport.Foundations.StepData
import OAI.Probability.SKSupport.Support.NoTerminalPlateau
import OAI.Probability.SKSupport.Support.GapCurvature
import OAI.Probability.SKSupport.Diffusion.Uniqueness

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem minimizer_full_support_actual (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ)
    {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) :
    μ.support=univ ∧ StrictMonoOn (extend γ.val) (Ico (0:ℝ) 1) ∧
    ∀ t ∈ Ico (0:ℝ) 1, squareMoment W γ (diffusion W γ) t=t ∧ curvatureMoment W γ t=1 := by
  have hh := SupportDeterministic.Variation.full_support_of_contact_and_gap_curvature
    (γ.original_deterministic) (stieltjes_deterministic γ hμ)
    (squareMoment_continuousOn W γ) (curvatureMoment_continuousOn_unit W γ)
    (fun t ht => squareMoment_hasDerivAt W γ ht.1 ht.2) (squareMoment_zero W γ)
    (minimizer_contact W γ hmin hμ) (minimizer_no_terminal_plateau W γ hmin)
    (fun a b c ha hab hb hc hconst => positive_gap_curvature W γ ha hab hb hc hconst)
    (fun a b ha hab hb hconst => zero_gap_curvature W γ ha hab hb hconst)
  have ha := SupportDeterministic.Variation.derivative_eq_one_of_full_contact hh.2.2
    (fun t ht => squareMoment_hasDerivAt W γ ht.1 ht.2)
    (squareMoment_hasDerivWithinAt W γ (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1))
  exact ⟨hh.1,hh.2.1,fun t ht => ⟨hh.2.2 t ht,ha t ht⟩⟩

theorem full_support (W : BrownianSystem Ω) (γ : OrderParameter)
    (hmin : IsMinimizer W γ) : FullSupportConclusion W γ := by
  have hμ := parameterMeasure_isStieltjes γ
  have hs := minimizer_full_support_actual W γ hmin hμ
  refine ⟨⟨parameterMeasure γ,hμ⟩,⟨diffusion W γ,diffusion_isDiffusion W γ⟩,
    fun μ hμ => (minimizer_full_support_actual W γ hmin hμ).1,?_,?_⟩
  · intro a b hab
    have hh := hs.2.1 a.property b.property hab
    simpa only [extend,dite_eq_left a.property,dite_eq_left b.property] using hh
  · intro X hX t
    have he : X (Real.toNNReal t)=ᵐ[W.law] diffusion W γ (Real.toNNReal t) := by
      filter_upwards [diffusion_uniqueness W γ hX] with ξ hξ
      apply hξ
      rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ t.property.1,NNReal.coe_one]
      exact t.property.2.le
    have hq : squareMoment W γ X t=squareMoment W γ (diffusion W γ) t := by
      apply integral_congr_ae
      filter_upwards [he] with ξ hξ
      rw [hξ]
    have ha : (∫ ξ, (curvature W γ t (X (Real.toNNReal t) ξ))^2 ∂W.law)=curvatureMoment W γ t := by
      apply integral_congr_ae
      filter_upwards [he] with ξ hξ
      rw [hξ]
    rw [hq,ha]
    exact hs.2.2 t t.property

end ZeroTemperatureSK

end
end

end OAI
