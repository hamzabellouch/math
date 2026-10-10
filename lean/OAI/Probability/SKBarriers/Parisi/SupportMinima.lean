import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFSupportDuality

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_continuous_integrable (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) : Integrable f (μ : Measure ℝ) := by
  have H := hf.integrableOn_Icc (μ:=(μ : Measure ℝ))
  rw [IntegrableOn,Measure.restrict_eq_self_of_ae_mem (supported_probability_ae μ hμ)] at H
  exact H

theorem support_minima_of_integral_le (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {f : ℝ → ℝ} (hf : Continuous f)
    (hmin : ∀ q∈Icc (0:ℝ) 1, (∫ x, f x ∂(μ : Measure ℝ))≤f q) :
    ∀ q∈(μ : Measure ℝ).support,
      q∈Icc (0:ℝ) 1 ∧ f q=(∫ x, f x ∂(μ : Measure ℝ)) ∧
      ∀ r∈Icc (0:ℝ) 1, f q≤f r := by
  let C := ∫ x, f x ∂(μ : Measure ℝ)
  have HI := supported_continuous_integrable μ hμ hf.continuousOn
  have Hn : ∀ᵐ x ∂(μ : Measure ℝ), 0≤f x-C := by
    filter_upwards [supported_probability_ae μ hμ] with x hx
    exact sub_nonneg.mpr (hmin x hx)
  have Hz : ∫ x, (f x-C) ∂(μ : Measure ℝ)=0 := by
    rw [integral_sub HI (integrable_const C),integral_const,probReal_univ,one_smul]
    exact sub_self _
  have He : ∀ᵐ x ∂(μ : Measure ℝ), f x=C := by
    have H := (integral_eq_zero_iff_of_nonneg_ae Hn (HI.sub (integrable_const C))).mp Hz
    filter_upwards [H] with x hx
    exact sub_eq_zero.mp hx
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    (isClosed_eq hf continuous_const) He
  have HD := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  intro q hq
  have Hq : f q=C := HS hq
  exact ⟨HD hq,Hq,fun r hr => Hq ▸ hmin r hr⟩

end SK.Analytic

end
end

end OAI
