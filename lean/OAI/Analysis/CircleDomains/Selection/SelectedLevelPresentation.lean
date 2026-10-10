import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanCodeLevels
import OAI.Analysis.CircleDomains.Selection.PhysicalRealCodeLevels

namespace OAI

/-! Presentations of selected real and mean coordinates, retaining
their functions, compact laws, and the data for subsequent code-law bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

structure RealCoordinatePresentation (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) where
  coordinate : PhysicalRealCoordinate d π
  graph_eq : C.graph = circleBandGraph d.quotientDomain coordinate.quotient
  mask_eq_univ : C.mask = univ
  physical_eq : ∀ x, (coordinate.physical x : UnitAddCircle) = C.physical x
  band_width : ∀ s, C.upper s - C.lower s =
    limsup coordinate.quotient (𝓝[d.quotientDomain] s.val) -
      liminf coordinate.quotient (𝓝[d.quotientDomain] s.val)
  compactSupport : Set ℂ
  isCompact_support : IsCompact compactSupport
  zero_off : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ compactSupport →
    coordinate.quotient (π (z : Sphere)) = 0
  zero_infty : OnePoint.infty ∈ d.physicalDomain → coordinate.quotient (π OnePoint.infty) = 0

structure MeanCoordinatePresentation (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) where
  arcs : Set C(PathTime, Sphere)
  diskArcs : Set C(PathTime, ℂ)
  compact_diskArcs : IsCompact diskArcs
  terminal_diskArcs : diskArcs ⊆ diskTerminalArcSet
  law : ProbabilityMeasure arcs
  map : C(Sphere, ℂ)
  arcMap : arcs → diskArcs
  measurable_arcMap : Measurable arcMap
  arcMap_eq : ∀ γ : arcs, (arcMap γ).val = map.comp γ.val
  neighborhood : Set Sphere
  mask : Set Sphere
  open_neighborhood : IsOpen neighborhood
  closed_mask : IsClosed mask
  excludes_infty : π OnePoint.infty ∉ mask
  boundary_domain : mask \ interior mask ⊆ d.quotientDomain
  singular : Sphere
  singular_eq : (C.singular : Sphere) = singular
  singular_dust : singular ∈ d.dust
  singular_mask : singular ∈ mask
  singular_outside : singular ∉ neighborhood
  punctured_mask : mask \ {singular} ⊆ neighborhood
  nonzero : ∀ x ∈ neighborhood, map x ≠ 0
  unit_bound : ∀ x ∈ neighborhood, ‖map x‖ ≤ 1
  strict_bound : ∀ x ∈ mask \ d.quotientDomain, ‖map x‖ < 1
  injective_arcs : ∀ γ : arcs, InjOn map (range γ.val ∪ neighborhood)
  mean : SmoothMeanPeriodData hsch diskArcs terminal_diskArcs (law.map arcMap) map
    d.physicalDomain d.quotientDomain neighborhood mask singular π
  graph_eq : C.graph = periodBandGraph d.quotientDomain mask singular mean.patch mean.branch

abbrev SelectedLevelPresentation (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val)) :=
  Sum (RealCoordinatePresentation d π C) (MeanCoordinatePresentation hsch d π C)


variable [BorelSpace C(PathTime, Sphere)]

theorem SelectedLevelPresentation.generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hdust : d.dust = d.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
    (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ d.quotientDomainᶜ)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hsep : UnitDiskCrosscutSeparation)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (R : SelectedLevelPresentation hsch d π C)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight)
    (hsingular : (C.singular : Sphere) ∈ Flags) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  cases R with
  | inl Q =>
      exact Q.coordinate.ranked_code_generic_levels rank hrank hcoarea hsard hsch d
        hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
        i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
        C Q.graph_eq hlevel hweights Q.isCompact_support Q.zero_off Q.zero_infty
  | inr Q =>
      exact Q.mean.ranked_code_generic_levels rank hrank hcoarea hsard hsch d
        hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
        i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
        Q.arcs Q.diskArcs Q.compact_diskArcs Q.terminal_diskArcs Q.law Q.map Q.arcMap
        Q.measurable_arcMap Q.arcMap_eq hsep Q.neighborhood Q.mask Q.open_neighborhood
        Q.closed_mask Q.excludes_infty Q.boundary_domain Q.singular (Q.singular_eq ▸ hsingular)
        Q.singular_mask Q.singular_outside Q.punctured_mask Q.nonzero Q.unit_bound Q.strict_bound
        Q.injective_arcs C Q.graph_eq hlevel hweights

end CircleDomainRigidity

end

end OAI
