import OAI.Analysis.CircleDomains.Sobolev.CircleWeightedCoarea
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodData

namespace OAI

/-! The actual masked mean-period levels have finite weighted physical
length almost everywhere, as required by the subsequent barrier step. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem SmoothMeanPeriodData.ae_finite_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) (hS : IsOpen S)
    {b : Sphere} (hbU : b ∉ U) (hMS : M \ {b} ⊆ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in G ∩ π ⁻¹' {x | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch},
        g p ∂(μH[1] : Measure Sphere)) < ∞ := by
  let D := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S
  have hD : IsOpen D := (hG.preimage OnePoint.continuous_coe).inter
    (hS.preimage (hπ.comp OnePoint.continuous_coe))
  apply ae_finite_spherical_circle_weighted_levels hcoarea hD Q.physical_smooth
    Q.physical_energy _ _ g hg hg2
  intro θ z hz
  have hzU := hPU z hz.1
  have hv := (Q.domain_value (π (z : Sphere)) hzU θ).mp hz.2
  have hzS : π (z : Sphere) ∈ S := hMS ⟨hv.1, fun h => hbU (h ▸ hzU)⟩
  refine ⟨⟨hz.1, hzS⟩, ?_⟩
  change Q.physical z = θ
  rw [Q.physical_value z hz.1 hzS]
  exact hv.2

end CircleDomainRigidity

end

end OAI
