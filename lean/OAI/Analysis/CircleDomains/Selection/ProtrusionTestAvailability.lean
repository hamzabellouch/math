import OAI.Analysis.CircleDomains.Selection.ProtrusionAlternatives
import OAI.Analysis.CircleDomains.Modulus.SelectableBarrierExclusion
import OAI.Analysis.CircleDomains.Selection.CoordinateExclusionTest

namespace OAI

/-! The local real/mean alternative gives an actual compatible open test
at every protruding marked component. All exclusion data are constructed. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_protrusion_exclusion_test
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
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
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
    (s : S) (hqs : π q = σ s) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust (σ s) g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 (σ s), ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (EStar : Set Sphere) (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior base.anchor)
    (hinfE : π OnePoint.infty ∈ interior base.anchor)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ base.levels i} ≤ base.levelWeights i x)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor)
    (harea : ExteriorCoefficientAreaTheorem)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar)
    (hconn : IsConnected base.physicalDomain)
    (hinfEStar : π OnePoint.infty ∈ interior EStar)
    (B₀ : Set base.dust) (p : B₀) (hp : p.val.val = σ s) :
    ∃ T' : CoordinateExclusionTest hsch base π B₀ (B / 4),
      T'.mark = p ∧ T'.coordinate.CompatibleWith Candidates ∧
      (p, (finiteSourceMap A.function (A.plane_open_embedding hG).1,
        A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈ T'.neighborhood := by
  classical
  have hπG : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain →
      π (z : Sphere) ∈ base.quotientDomain := by
    intro z hz
    rw [← he ⟨_, hz⟩]
    exact (base.domainEquiv ⟨_, hz⟩).property
  have hpre : π ⁻¹' base.quotientDomain ⊆ base.physicalDomain := by
    intro z hz
    by_contra hn
    exact hbad z hn hz
  have hBImage : base.dust = π '' base.physicalDomainᶜ := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z, rfl⟩ := hsurj x
      refine ⟨z, ?_, rfl⟩
      intro hz
      have hπz : π z ∈ base.quotientDomain := by
        rw [← he ⟨_, hz⟩]
        exact (base.domainEquiv ⟨_, hz⟩).property
      exact (show π z ∈ base.quotientDomainᶜ from hdust ▸ hx) hπz
    · rintro _ ⟨z, hz, rfl⟩
      exact hdust.symm ▸ hbad z hz
  obtain hreal | hmean := exists_protrusion_barrier_or_selectable_mean rank hrank
    hcoarea hsard hsch hsep base hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad
    Flags hFlags hFlagsB C presentation hlevel hweights hmarked hsingular hP hunique
    ω hω hωsum hLusin hfiber harcs previous hprevious hweighted hcollar hselect
    Candidates label hflags hgraphs E T hq s hqs hinf hseparated D hnest hshrink
    hanchor hfinite EStar hE hEU hEStar hEStarE hinfE hpoint C₀ hC₀ hderiv
    hstandard hpath hdual hlift B R hB hR hfar
  · obtain ⟨P, hsmall⟩ := hreal
    obtain ⟨c, hcomp, W, _, hmem, hmemSized⟩ := P.exists_selectable_exclusion
      hweighted hsch harea hG hconn hU hdense hπ hr he hBImage hπG hpre
      (interior_subset hinfE) p.val T hq
      (fun n => (D n).isOpen_region hπ hclosed hsurj hr)
      (fun n => by rw [hqs]; exact (D n).point_mem_region hsurj (by
        intro hi
        have hx : σ s ∈ base.dust := hp ▸ p.val.property
        have hπi : π OnePoint.infty ∈ base.quotientDomain := hEU (interior_subset hinfE)
        exact (show σ s ∈ base.quotientDomainᶜ from hdust ▸ hx) (hi ▸ hπi)))
      hzero (fun z hz => quotientNormalizedMap_physical base.domainEquiv π he A.function z hz)
      (Subset.refl _) (ENNReal.toReal_lt_of_lt_ofReal hsmall) hinfEStar
      Candidates label hflags hgraphs
    exact ⟨⟨p, c, Sum.inl W⟩, rfl, hcomp, rfl, hmemSized _ _⟩
  · obtain ⟨c, hcomp, ⟨P⟩, hsing, W, hbound, hmem⟩ := hmean
    let W' : MeanExclusionTest hsch base π c.coordinate p.val (B / 4) := {
      presentation := P
      function := A.function
      continuousOn := (A.plane_open_embedding hG).1
      center := A.center s
      radius := ⟨A.radius s, (A.bounds s).2.1⟩
      budgetRadius := R
      witness := W
      singular := Subtype.ext (hsing.trans hp.symm)
      source_bound := fun z hz => by have h := hbound z hz; linarith }
    exact ⟨⟨p, c, Sum.inr W'⟩, rfl, hcomp, rfl, hmem⟩

end CircleDomainRigidity

end

end OAI
