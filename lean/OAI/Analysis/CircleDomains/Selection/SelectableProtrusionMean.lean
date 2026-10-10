import OAI.Analysis.CircleDomains.Selection.SelectableRecursiveMean
import OAI.Analysis.CircleDomains.Selection.ProtrusionMeanExclusion
import OAI.Analysis.CircleDomains.Transfer.AnchoredMeanSourceBound
import OAI.Analysis.CircleDomains.Selection.MeanExclusionCongruence
import OAI.Analysis.CircleDomains.Selection.SizedMeanExclusion

namespace OAI

/-! The actual gated law at a protrusion gives a compatible selectable
mean test and an open exclusion containing the original sized map--disk
pair. The circuit bound comes from the fixed exterior anchor. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.exists_selectable_protrusion_mean
    {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
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
    (hweighted : WeightedPlanarScalarCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c))
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s) (htarget : L.data.target = σ s)
    (hp : L.data.target ≠ π OnePoint.infty)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
      ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate))
    (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      (c.coordinate.singular : Sphere) = σ s ∧
      ∃ W : MeanExclusionWitness c.coordinate A.function (A.plane_open_embedding hG).1
        (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩ R,
        (∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B) ∧
        ((finiteSourceMap A.function (A.plane_open_embedding hG).1,
          A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈
            W.sizedNeighborhood (B / 4) := by
  have hR0 : 0 ≤ R := (mul_nonneg (by norm_num) M.radius_pos.le).trans hR.le
  obtain ⟨δ, _, F₀, hF₀, hEq, K, hevent⟩ := L.eventually_protrusion_mean
    hsch hsep hcoarea hcollar hselect harcs hG hU hdense hdust hπ hclosed hsurj hr he hbad
    hp E T hq s hqs hseparated hR0 D hnest hshrink hanchor hfinite hcontours hgates
  obtain ⟨n, J, hJ, Q, ⟨N⟩⟩ := hevent.exists
  have hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J :=
    hJ ▸ (D n).point_mem_region hsurj hp
  obtain ⟨c, hc, hcomp, hpres, _, _⟩ := N.selectable rank hrank hcoarea hsard hsch hsep
    base hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad Flags hFlags hFlagsB
    C presentation hlevel hweights hmarked hsingular hP hunique ω L hLusin hfiber harcs
    previous hprevious Q hbJ hweighted he Candidates label
    (fun c hc x hx => Or.inl (hflags c hc hx)) hgraphs
  refine ⟨c, hcomp, hpres, ?_, ?_⟩
  · rw [hc, N.singular_eq, htarget]
  · rw [hc]
    let W := N.exclusion.congr_map (hF₁ := (A.plane_open_embedding hG).1) hEq
    have hanti : Antitone (fun n => (D n).region) :=
      antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
    have hNJ : Disjoint base.anchor (((↑) : ℂ → Sphere) '' jordanInterior J) := by
      rw [← hJ]
      exact hanchor.mono_right ((hanti (Nat.zero_le n)).trans subset_closure)
    exact ⟨W, N.boundary_norm_lt_of_anchor hNJ hfar, W.mem_sizedNeighborhood hB hR⟩

end CircleDomainRigidity

end

end OAI
