import OAI.Analysis.CircleDomains.Selection.RecursiveMeanCompatibility
import OAI.Analysis.CircleDomains.Rigidity.SelectableMaskedCoordinate
import OAI.Analysis.CircleDomains.Rigidity.OrderedMaskedSelection
import OAI.Analysis.CircleDomains.Topology.SubarcPointAvoidance

namespace OAI

/-! The recursive positive-law alternative constructs a selectable mean
coordinate with its concrete presentation. Finite compatibility is derived
from the preceding law estimates, while preserving the coordinate’s
Stokes budget and exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.selectable_mean_coordinate
    {O : Type*} [LinearOrder O] (rank : ℕ → O) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (Flags' : Set Sphere) (hFlags' : Flags'.Countable)
    (hFlagsB' : Flags' ⊆ base.quotientDomainᶜ) (hFlagsMono : Flags ⊆ Flags')
    (S M : Set Sphere) (b : Sphere) (hb : b ∈ Flags') (hbS : b ∉ S)
    (hboundary : M \ interior M ⊆ base.quotientDomain) (hMS : M \ {b} ⊆ S)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (ν : ProbabilityMeasure C(PathTime, Sphere))
    (hred : IsSubarcLawReduction (codePathLaw L.data L.law) ν)
    (hη : η.map Subtype.val = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hFlagsHits : {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} ⊆ Flags')
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F
      base.physicalDomain base.quotientDomain S M b π)
    (hweighted : WeightedPlanarScalarCoarea)
    (hebase : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hstrict : ∀ x ∈ M \ base.quotientDomain, ‖F x‖ < 1)
    (hS : IsOpen S) (hM : IsClosed M) (hinftyM : π OnePoint.infty ∉ M) (hbM : b ∈ M)
    (N : MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (hN : N.graph = periodBandGraph base.quotientDomain M b Q.patch Q.branch)
    (hNb : (N.singular : Sphere) = b)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags')
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c)) :
    ∃ c : SelectableMaskedCoordinate base π, c.coordinate = N ∧
      c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) := by
  have hmiss : ∀ x ∈ (base.quotientDomainᶜ \ Flags') ∩ S,
      ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val := by
    intro x hx
    exact L.subarc_avoids_unmarked_point Flags' hFlagsHits hred η hη
      ⟨hdust.symm ▸ hx.1.1, hx.1.2⟩
  have hPU (z : ℂ) (hz : (z : Sphere) ∈ base.physicalDomain) :
      π (z : Sphere) ∈ base.quotientDomain := by
    rw [← hebase ⟨z, hz⟩]
    exact (base.domainEquiv ⟨z, hz⟩).property
  obtain ⟨c, hc, hmark⟩ := SelectableMaskedCoordinate.exists_of_mean hweighted hsch base hG
    π hπ hPU K hKS (η.map f) F S M hS b (hFlagsB' hb) hMS Q N hN
    Flags' hFlags' (fun x hx => hdust.symm ▸ hFlagsB' hx)
  have hcomp (n : ℕ) (ls : Fin n → ℕ) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.quotientDomainᶜ \ Flags')
          (periodBandGraph base.quotientDomain M b Q.patch Q.branch) previous.graph ls) = 0 :=
    L.mean_coordinate_compatible rank hrank hcoarea hsard hsch hsep base
      hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad Flags hFlags hFlagsB C presentation
      hlevel hweights hmarked hsingular hP hunique ω hLusin hfiber harcs previous hprevious
      Flags' hFlags' hFlagsB' hFlagsMono S M b hb hbS hboundary hMS A K hK hKS η F f hf
      hmap ν hred hη h0 h1 hF hinj hmiss Q n ls
  refine ⟨c, hc, ⟨?_, ?_⟩, ?_⟩
  · exact fun a ha => (hflags a ha).trans hmark
  · intro n q hq
    rw [hc, hN]
    have hz := hcomp n (label ∘ q)
    rw [UngatedRealTest.freeComponentFailure_congr_selected (base.quotientDomainᶜ \ Flags')
      (periodBandGraph base.quotientDomain M b Q.patch Q.branch) previous.graph
      (fun i : Fin n => (q i).coordinate.graph) (label ∘ q) id
      (fun i => (hgraphs (q i) (hq i)).symm)] at hz
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ id) hz
    intro x hx
    exact ⟨hdust ▸ hx.1, fun hm => hx.2 (hmark hm)⟩
  · refine ⟨{
      arcs := A
      diskArcs := K
      compact_diskArcs := hK
      terminal_diskArcs := hKS
      law := η
      map := F
      arcMap := f
      measurable_arcMap := hf
      arcMap_eq := hmap
      neighborhood := S
      mask := M
      open_neighborhood := hS
      closed_mask := hM
      excludes_infty := hinftyM
      boundary_domain := hboundary
      singular := b
      singular_eq := by rw [hc]; exact hNb
      singular_dust := hdust.symm ▸ hFlagsB' hb
      singular_mask := hbM
      singular_outside := hbS
      punctured_mask := hMS
      nonzero := h0
      unit_bound := h1
      strict_bound := hstrict
      injective_arcs := hF
      mean := Q
      graph_eq := by rw [hc]; exact hN }⟩

end CircleDomainRigidity

end

end OAI
