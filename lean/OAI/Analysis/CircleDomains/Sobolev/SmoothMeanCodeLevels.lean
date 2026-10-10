import OAI.Analysis.CircleDomains.Rigidity.RankedCodeTraces
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanBandWeight

namespace OAI

/-! Generic prior levels for the actual smoothed mean and its masked
coordinate. The atlas and its weight estimates are derived from that
coordinate, not supplied as a generic-intersection hypothesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem SmoothMeanPeriodData.ranked_code_generic_levels
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
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (hsep : UnitDiskCrosscutSeparation)
    (S M : Set Sphere) (hS : IsOpen S) (hM : IsClosed M)
    (hinftyM : π OnePoint.infty ∉ M)
    (hboundary : M \ interior M ⊆ d.quotientDomain)
    (b : Sphere) (hb : b ∈ Flags) (hbM : b ∈ M) (hbS : b ∉ S)
    (hMS : M \ {b} ⊆ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ d.quotientDomain, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F
      d.physicalDomain d.quotientDomain S M b π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hgraph : C.graph = periodBandGraph d.quotientDomain M b Q.patch Q.branch)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  let : Countable Q.Index := Q.countableIndex
  let w : Sphere → UnitAddCircle := fun x =>
    diskMeanCircle hsch K hKS (η.map f) (F x) + (Q.error x : UnitAddCircle)
  have hmiss (j : Q.Index) : b ∉ Q.patch j :=
    fun hj => hbS (Q.patch_closure j (subset_closure hj))
  have hcompat : ∀ j k x, x ∈ Q.patch j → x ∈ Q.patch k → ∀ θ,
      (x, θ) ∈ circleBandGraph d.quotientDomain (Q.branch j) ↔
        (x, θ) ∈ circleBandGraph d.quotientDomain (Q.branch k) := by
    intro j k x hj hk θ
    obtain ⟨m, hm⟩ := Q.transition j k x hj hk
    exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hm) θ).symm
  have hlocal (j : Q.Index) (x : Sphere) (hx : x ∈ M ∩ Q.patch j) (θ : UnitAddCircle) :
      (x, θ) ∈ circleBandGraph d.quotientDomain (Q.branch j) ↔
        (θ, x) ∈ d.levels i := by
    rw [hlevel, mem_preimage, Prod.swap_prod_mk, hgraph,
      periodBandGraph_on_patch _ _ _ _ _ hmiss hcompat hx.2]
    exact (and_iff_right hx.1).symm
  have hband (j : Q.Index) (x : Sphere)
      (hx : x ∈ (d.quotientDomainᶜ ∩ M) ∩ Q.patch j) :
      ENNReal.ofReal (limsup (Q.branch j) (𝓝[d.quotientDomain] x) -
        liminf (Q.branch j) (𝓝[d.quotientDomain] x)) ≤ d.levelWeights i x := by
    rw [hweights]
    exact Q.branch_width_le_dustWeight hsch hsep A K hK hKS η F f hf hmap hdense hbS
      (by rw [hdust]) h0 hstrict hF C hgraph j ⟨hdust.symm ▸ hx.1.1, hx.1.2⟩ hx.2
  have hw (j : Q.Index) (x : Sphere) (hx : x ∈ d.quotientDomain ∩ Q.patch j) :
      (Q.branch j x : UnitAddCircle) = w x := by
    have hxS := Q.patch_closure j (subset_closure hx.2)
    dsimp only [w]
    rw [Q.branch_value j x hx.2, AddCircle.coe_add]
    congr 1
    rw [← diskMeanCircle_projection hsch hsep K hK hKS (η.map f),
      upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (Q.angle j) (h1 x hxS)),
      logarithmicCutChart_projection (Q.angle j) (h0 x hxS)]
  exact (ranked_code_period_generic_levels rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
    Q.patch Q.patch_open M hM hinftyM hboundary b hb
    (by
      rw [hweights]
      exact masked_singular_weight_ge_one Q.patch Q.branch C hgraph
        (hdust.symm ▸ hFlagsB hb) hbM)
    (fun θ x hx => by
      rw [hlevel, mem_preimage, Prod.swap_prod_mk, hgraph] at hx
      exact hx.1)
    (hMS.trans Q.cover) Q.branch Q.bound (fun j x _ => Q.bounded j x)
    Q.continuous Q.branch_smooth Q.branch_energy hband hlocal w hw
    (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S)
    ((hG.preimage OnePoint.continuous_coe).inter
      (hS.preimage (hπ.comp OnePoint.continuous_coe)))
    (fun _ hz => hz.1)
    (fun z hzG hzM => ⟨hzG, hMS ⟨hzM, fun heq => hFlagsB hb (heq ▸
      (show π (z : Sphere) ∈ d.quotientDomain from
        (he ⟨z, hzG⟩) ▸ (d.domainEquiv ⟨z, hzG⟩).property))⟩⟩)
    Q.physical Q.physical_smooth
    (fun z hz => Q.physical_value z hz.1 hz.2) Q.physical_energy).2

end CircleDomainRigidity

end

end OAI
