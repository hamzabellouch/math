import OAI.Analysis.CircleDomains.Rigidity.MaskedLevelData
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodConsequences

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure SelectableMaskedCoordinate (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) where
  coordinate : MaskedCoordinateData d.physicalDomain d.quotientDomain π
    (fun x : d.dust => x.val)
  flags : Set Sphere
  flags_countable : flags.Countable
  flags_dust : flags ⊆ d.dust
  weight_support : support coordinate.dustWeight ⊆ flags
  singular_marked : (coordinate.singular : Sphere) ∈ flags
  domain_unique : ∀ x ∈ d.quotientDomain,
    {t : UnitAddCircle | (x, t) ∈ coordinate.graph}.Subsingleton
  weighted : ∀ (g : Sphere → ℝ≥0∞), Measurable g →
    (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞ →
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in d.physicalDomain ∩ π ⁻¹' {x | (x, θ) ∈ coordinate.graph},
        g p ∂(μH[1] : Measure Sphere)) < ∞

namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

def CompatibleWith (c : SelectableMaskedCoordinate d π)
    (A : Set (SelectableMaskedCoordinate d π)) : Prop :=
  (∀ a ∈ A, a.flags ⊆ c.flags) ∧
  ∀ (n : ℕ) (q : Fin n → SelectableMaskedCoordinate d π), (∀ i, q i ∈ A) →
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.flags) c.coordinate.graph
        (fun i : Fin n => (q i).coordinate.graph) id) = 0

theorem CompatibleWith.mono {c : SelectableMaskedCoordinate d π}
    {A B : Set (SelectableMaskedCoordinate d π)}
    (h : c.CompatibleWith B) (hAB : A ⊆ B) : c.CompatibleWith A :=
  ⟨fun a ha => h.1 a (hAB ha), fun n q hq => h.2 n q (fun i => hAB (hq i))⟩

def priorLevels (c : ℕ → SelectableMaskedCoordinate d π) :
    PriorLevelFamily d.physicalDomain π where
  graph i := (c i).coordinate.graph
  closed i := (c i).coordinate.graph_closed
  weighted i := (c i).weighted

def pathData (c : ℕ → SelectableMaskedCoordinate d π) : PathCodeData Sphere Sphere :=
  maskedLevelData d π (fun i => (c i).coordinate)

theorem point_bound (c : ℕ → SelectableMaskedCoordinate d π)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (i : ℕ) (x : Sphere) :
    volume {t | (t, x) ∈ (pathData c).levels i} ≤ (pathData c).levelWeights i x :=
  maskedLevelData.point_bound _ hBU (fun i => (c i).domain_unique) i x

theorem weight_finite (c : ℕ → SelectableMaskedCoordinate d π) (i : ℕ) :
    (∑' x, (pathData c).levelWeights i x ^ 2) < ∞ :=
  maskedLevelData.weight_finite _ i

theorem common_flags (c : ℕ → SelectableMaskedCoordinate d π) :
    (⋃ i, (c i).flags).Countable ∧ (⋃ i, (c i).flags) ⊆ d.dust ∧
      ∀ i, support ((pathData c).levelWeights i) ⊆ ⋃ j, (c j).flags := by
  refine ⟨countable_iUnion (fun i => (c i).flags_countable), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (c i).flags_dust hi
  · intro i x hx
    exact mem_iUnion.mpr ⟨i, (c i).weight_support hx⟩

theorem unique_free_trace (c : ℕ → SelectableMaskedCoordinate d π)
    (x : Sphere) (hx : x ∈ d.dust \ ⋃ i, (c i).flags) (i : ℕ) (a b : UnitAddCircle)
    (ha : (a, x) ∈ (pathData c).levels i) (hb : (b, x) ∈ (pathData c).levels i) : a = b :=
  maskedLevelData.unique_free_trace _ _ (common_flags c).2.2 x hx i a b ha hb

end SelectableMaskedCoordinate

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem SmoothMeanPeriodData.domain_fiber_subsingleton
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (x : Sphere) (hx : x ∈ U) :
    {t : UnitAddCircle | (x, t) ∈ periodBandGraph U M b Q.patch Q.branch}.Subsingleton := by
  intro a ha b hb
  exact ((Q.domain_value x hx a).mp ha).2.symm.trans ((Q.domain_value x hx b).mp hb).2

namespace SelectableMaskedCoordinate

 theorem exists_of_mean
    (hcoarea : WeightedPlanarScalarCoarea) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → π (z : Sphere) ∈ d.quotientDomain)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (S M : Set Sphere) (hS : IsOpen S) (b : Sphere) (hbU : b ∉ d.quotientDomain)
    (hMS : M \ {b} ⊆ S)
    (Q : SmoothMeanPeriodData hsch K hKS η F d.physicalDomain d.quotientDomain S M b π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val))
    (hgraph : C.graph = periodBandGraph d.quotientDomain M b Q.patch Q.branch)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust) :
    ∃ c : SelectableMaskedCoordinate d π, c.coordinate = C ∧ flags ⊆ c.flags := by
  obtain ⟨Z, hZ, hfZ, hZB, hsing, hweights⟩ :=
    maskedLevelData.exists_countable_flags (fun _ => C) flags hflags hflagsB
  refine ⟨{
    coordinate := C
    flags := Z
    flags_countable := hZ
    flags_dust := hZB
    weight_support := hweights 0
    singular_marked := hsing 0
    domain_unique := ?_
    weighted := ?_ }, rfl, hfZ⟩
  · intro x hx
    rw [hgraph]
    exact Q.domain_fiber_subsingleton hsch K hKS η F x hx
  · intro g hg henergy
    rw [hgraph]
    exact Q.ae_finite_weighted_levels hcoarea hsch K hKS η F hG hS hbU hMS hπ hPU
      g hg henergy

 theorem exists_of_real
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (Q : PhysicalRealCoordinate d π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain Q.quotient)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust) :
    ∃ c : SelectableMaskedCoordinate d π, c.coordinate = C ∧ flags ⊆ c.flags := by
  obtain ⟨Z, hZ, hfZ, hZB, hsing, hweights⟩ :=
    maskedLevelData.exists_countable_flags (fun _ => C) flags hflags hflagsB
  refine ⟨{
    coordinate := C
    flags := Z
    flags_countable := hZ
    flags_dust := hZB
    weight_support := hweights 0
    singular_marked := hsing 0
    domain_unique := ?_
    weighted := ?_ }, rfl, hfZ⟩
  · intro x hx a ha b hb
    rw [hgraph] at ha hb
    exact ((circleBandGraph_on_open hU Q.quotient_continuous hx).mp ha).symm.trans
      ((circleBandGraph_on_open hU Q.quotient_continuous hx).mp hb)
  · intro g hg henergy
    rw [hgraph]
    exact physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π
      (fun x => (he x).symm) Q g hg henergy

end SelectableMaskedCoordinate

end CircleDomainRigidity

end

end OAI
