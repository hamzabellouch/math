import Mathlib
import OAI.Geometry.WeakHessian.Entropy.TendstoRenyiGap
import OAI.Geometry.WeakHessian.Calculus.RnDerivRestrictReference

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma cd_entropy_bound_on_finite_region {m μ₀ μ₁ μt : Measure X} [SigmaFinite m]
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μt]
    {π : Measure Y} [IsProbabilityMeasure π] {e₀ e₁ : Y → X}
    (he₀ : Measurable e₀) (he₁ : Measurable e₁)
    (hm₀ : Measure.map e₀ π = μ₀) (hm₁ : Measure.map e₁ π = μ₁)
    (hE₀ : FiniteEntropy m μ₀) (hE₁ : FiniteEntropy m μ₁)
    {Q : Set X} (hQ : MeasurableSet Q) (hQfin : m Q < ∞)
    (hs₀ : ∀ᵐ x ∂μ₀, x ∈ Q) (hs₁ : ∀ᵐ x ∂μ₁, x ∈ Q) (hst : ∀ᵐ x ∂μt, x ∈ Q)
    {θ : Y → ℝ} (hθ : Measurable θ) (hθ0 : ∀ᵐ y ∂π, 0 ≤ θ y)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ y ∂π, θ y ^ 2 ≤ C) {K t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) {d : ℕ → ℝ} (hd : ∀ n, 1 < d n)
    (hdlim : Tendsto (fun n => 1/d n) atTop (𝓝 0))
    (hcd : ∀ n, (∫⁻ y, tauCoeff K (d n) (1-t) (θ y)*(μ₀.rnDeriv m (e₀ y))^(-1/(d n)) +
      tauCoeff K (d n) t (θ y)*(μ₁.rnDeriv m (e₁ y))^(-1/(d n)) ∂π) ≤ renyiIntegral m μt (d n)) :
    FiniteEntropy m μt ∧ entropyReal m μt ≤ (1-t)*entropyReal m μ₀+t*entropyReal m μ₁ -
      K/2*t*(1-t)*(∫ y, θ y^2 ∂π) := by
  let : IsFiniteMeasure (m.restrict Q) := ⟨by simpa using hQfin⟩
  have HE₀ := (finiteEntropy_restrict_reference_iff hQ hs₀).mpr hE₀
  have HE₁ := (finiteEntropy_restrict_reference_iff hQ hs₁).mpr hE₁
  have hr₀ : ∀ᵐ y ∂π, μ₀.rnDeriv m (e₀ y) = μ₀.rnDeriv (m.restrict Q) (e₀ y) := by
    have H : ∀ᵐ x ∂Measure.map e₀ π, μ₀.rnDeriv m x = μ₀.rnDeriv (m.restrict Q) x := by
      rw [hm₀]
      exact rnDeriv_restrict_reference_ae hQ hE₀.1 hs₀
    exact ae_of_ae_map he₀.aemeasurable H
  have hr₁ : ∀ᵐ y ∂π, μ₁.rnDeriv m (e₁ y) = μ₁.rnDeriv (m.restrict Q) (e₁ y) := by
    have H : ∀ᵐ x ∂Measure.map e₁ π, μ₁.rnDeriv m x = μ₁.rnDeriv (m.restrict Q) x := by
      rw [hm₁]
      exact rnDeriv_restrict_reference_ae hQ hE₁.1 hs₁
    exact ae_of_ae_map he₁.aemeasurable H
  have H := cd_entropy_bound_of_dimensions (μt := μt) (K := K) he₀ he₁ hm₀ hm₁ HE₀ HE₁ hθ hθ0 hC hb ht ht1 hd hdlim
    (fun n => ?_)
  · have HE := (finiteEntropy_restrict_reference_iff hQ hst).mp H.1
    refine ⟨HE,?_⟩
    simpa only [entropyReal_restrict_reference hQ HE.1 hst,
      entropyReal_restrict_reference hQ hE₀.1 hs₀,entropyReal_restrict_reference hQ hE₁.1 hs₁] using H.2
  · rw [← renyiIntegral_restrict_reference hQ hst (hd n)]
    refine (lintegral_congr_ae ?_).trans_le (hcd n)
    filter_upwards [hr₀,hr₁] with y hy₀ hy₁
    rw [hy₀,hy₁]
end WeakHessian

end
end InlinedFile0

end OAI
