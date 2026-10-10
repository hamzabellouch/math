import OAI.Analysis.CircleDomains.Probability.RecursiveLawLevelEstimates
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodConsequences

namespace OAI

/-! A recursive positive law gives compatibility for the next smoothed
mean. Generic prior intersections follow from its retained real and mean
data and candidate budgets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.mean_coordinate_compatible
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
    (hmiss : ∀ x ∈ (base.quotientDomainᶜ \ Flags') ∩ S,
      ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F
      base.physicalDomain base.quotientDomain S M b π)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (base.quotientDomainᶜ \ Flags')
        (periodBandGraph base.quotientDomain M b Q.patch Q.branch) previous.graph labels) = 0 := by
  have hg := L.generic_prior_levels rank hrank hcoarea hsard hsch hsep base
    hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad Flags hFlags hFlagsB C presentation
    hlevel hweights hmarked hsingular hP hunique ω
  have hgeneric (i : ℕ) : ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, θ) ∈ previous.graph i} γ
        ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (base.quotientDomainᶜ \ Flags'), (x, θ) ∈ previous.graph i := by
    rw [hprevious i]
    filter_upwards [hg i] with θ hθ
    refine ⟨hθ.1, ?_⟩
    filter_upwards [hθ.2] with γ hγ
    rintro ⟨x, ⟨hxγ, hxB, hxF⟩, hxi⟩
    exact hγ ⟨x, ⟨hxγ, hxB, fun hx => hxF (hFlagsMono hx)⟩, hxi⟩
  have hσU : IsSigmaCompact base.quotientDomain := by
    let : LocallyCompactSpace base.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  apply Q.compatibility hsch hsep hLusin π hπ hsurj hfiber hG
    (show IsCompact base.dust from by rw [hdust]; exact hU.isClosed_compl.isCompact)
    (by rwa [hdust])
    (by rintro _ ⟨x, hx, rfl⟩; exact hdust.symm ▸ hbad x hx)
    hσU hdense hFlags'
    (disjoint_left.mpr (fun x hx hxF => hFlagsB' hxF hx)) b hb hbS hboundary hMS harcs
    A K hK hKS η F f hf hmap (codePathLaw L.data L.law) ν hred hη h0 h1 hF hinj hmiss
    previous.graph previous.closed previous.length hgeneric n labels

end CircleDomainRigidity

end

end OAI
