import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.SobolevSubdifferential
import OAI.Geometry.WeakHessian.LocalBounds.ContactUniqueness

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile24
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m]

theorem RCD.compact_entropy_subgradient_any {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    {η : Measure (Curve X)} [IsProbabilityMeasure η] (hbη : BoundedTracks η)
    (hoη : IsOptimalCoupling (endpointCoupling η) μ ν)
    {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hdual : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂η,φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy η ≤
      ∫ x,2*w x*gamma m φ w x ∂m := by
  obtain ⟨π,f,g,hπ,hb,hgeo,hopt,hf,hg,hd,hc,hent⟩ :=
    hrcd.compact_sobolev_entropy_subdifferential hN hfin w hw hwm hB hwn hwB μ ν hμ o R hsμ hsν hCt hdν
  have he := optimal_planEnergy_eq hopt hoη hb.integrable_length_sq hbη.integrable_length_sq
  have hcφ : ∀ᵐ γ ∂(π:Measure (Curve X)),φ (γ timeZero)+ψ (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := by
    apply contact_of_integral_eq hb hb.integrable_length_sq hφ hψ hdual
    have H := contact_integral_eq hbη hφ hψ hcontact
    rw [hoη.1.interpolation_endpoints.1,hoη.1.interpolation_endpoints.2,← he] at H
    simpa only [hopt.1.interpolation_endpoints.1,hopt.1.interpolation_endpoints.2] using H
  have hpair := hπ.contact_entropy_pairing_eq hfin
    (hrcd.1.global_localGradientParallelogram hfin o hrcd.2) hb hgeo hf hφ hw hwm hwn
    (hopt.1.interpolation_endpoints.1.trans hμ) hd hdual hc hcφ
  rwa [he,hpair] at hent
end WeakHessian

end
end InlinedFile24

end OAI
