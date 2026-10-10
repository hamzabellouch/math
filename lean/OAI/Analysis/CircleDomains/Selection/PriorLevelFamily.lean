import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoordinateCoarea
import OAI.Analysis.CircleDomains.Sobolev.PeriodWeightedCoarea

namespace OAI

/-! The exact weighted-level data consumed by the barrier construction.
Both earlier real coordinates and the constructed masked means supply it. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

structure PriorLevelFamily (G : Set Sphere) (π : Sphere → Sphere) where
  graph : ℕ → Set (Sphere × UnitAddCircle)
  closed : ∀ i, IsClosed (graph i)
  weighted : ∀ (i : ℕ) (g : Sphere → ℝ≥0∞), Measurable g →
    (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞ →
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in G ∩ π ⁻¹' {x | (x, θ) ∈ graph i}, g p ∂(μH[1] : Measure Sphere)) < ∞

 theorem PriorLevelFamily.length
    {G : Set Sphere} {π : Sphere → Sphere} (P : PriorLevelFamily G π) (i : ℕ) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (μH[1] : Measure Sphere) (G ∩ π ⁻¹' {x | (x, θ) ∈ P.graph i}) < ∞ := by
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    P.weighted i (fun _ => 1) measurable_const (by simp)

variable [MeasurableSpace C(PathTime, Sphere)]

 def PriorLevelFamily.ofReal (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (he : ∀ y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : ℕ → PhysicalRealCoordinate d π) : PriorLevelFamily d.physicalDomain π where
  graph i := circleBandGraph d.quotientDomain (Q i).quotient
  closed i := (isCompact_circleBandGraph (fun x _ => by
    rw [abs_of_nonneg ((Q i).quotient_unit x).1]
    exact ((Q i).quotient_unit x).2)).isClosed
  weighted i := physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π he (Q i)

 def PriorLevelFamily.ofMeans
    (hcoarea : WeightedPlanarScalarCoarea) (hsch : PlanarSchoenflies)
    {G U : Set Sphere} (hG : IsOpen G) {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (K : ℕ → Set C(PathTime, ℂ)) (hKS : ∀ i, K i ⊆ diskTerminalArcSet)
    (η : ∀ i, ProbabilityMeasure (K i)) (F : ℕ → C(Sphere, ℂ))
    (S M : ℕ → Set Sphere) (hS : ∀ i, IsOpen (S i)) (b : ℕ → Sphere)
    (hbU : ∀ i, b i ∉ U) (hMS : ∀ i, M i \ {b i} ⊆ S i)
    (Q : ∀ i, SmoothMeanPeriodData hsch (K i) (hKS i) (η i) (F i) G U (S i) (M i) (b i) π) :
    PriorLevelFamily G π where
  graph i := periodBandGraph U (M i) (b i) (Q i).patch (Q i).branch
  closed i := (Q i).closed
  weighted i := (Q i).ae_finite_weighted_levels hcoarea hsch (K i) (hKS i) (η i) (F i)
    hG (hS i) (hbU i) (hMS i) hπ hPU

end CircleDomainRigidity

end

end OAI
