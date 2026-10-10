import OAI.Analysis.CircleDomains.Selection.SelectableProtrusionMean
import OAI.Analysis.CircleDomains.Probability.GatedRecursiveLaw
import OAI.Analysis.CircleDomains.Topology.RetargetedCollars
import OAI.Analysis.CircleDomains.Selection.SlackRealExclusion

namespace OAI

/-! At a marked-component protrusion, either a small compatible real
barrier exists, or positive-law duality constructs a compatible mean
coordinate with an open sized exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_protrusion_barrier_or_selectable_mean
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
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    (∃ P : CompatibleLevelBarrier base π previous Flags EStar
      (fun n => (D n).region) (quotientNormalizedMap base.domainEquiv A.function) T.closedGate,
      P.controlledSize < ENNReal.ofReal T.selectionThreshold) ∨
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      (c.coordinate.singular : Sphere) = σ s ∧
      ∃ W : MeanExclusionWitness c.coordinate A.function (A.plane_open_embedding hG).1
        (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩ R,
        (∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B) ∧
        ((finiteSourceMap A.function (A.plane_open_embedding hG).1,
          A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈
            W.sizedNeighborhood (B / 4) := by
  classical
  by_cases hsmall : ∃ P : CompatibleLevelBarrier base π previous Flags EStar
      (fun n => (D n).region) (quotientNormalizedMap base.domainEquiv A.function) T.closedGate,
      P.controlledSize < ENNReal.ofReal T.selectionThreshold
  · exact Or.inl hsmall
  apply Or.inr
  have hinfty : π OnePoint.infty ∉ base.dust := by
    rw [hdust, ← he ⟨_, hinf⟩]
    exact not_not.mpr (base.domainEquiv ⟨_, hinf⟩).property
  have hpB : σ s ∈ base.dust := by
    rw [← hqs, hdust]
    exact hbad q hq
  have hp : σ s ≠ π OnePoint.infty := fun h => hinfty (h ▸ hpB)
  have hlevels : ∀ i, base.levels i = Prod.swap ⁻¹' previous.graph i := by
    intro i
    rw [hlevel, hprevious]
  have hweightsFinite : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞ := by
    intro i
    rw [hweights]
    exact (C i).dustWeight_square_sum
  have hunique' : ∀ x ∈ base.dust \ Flags, ∀ i t u,
      (t, x) ∈ base.levels i → (u, x) ∈ base.levels i → t = u := by
    simpa only [hdust] using hunique
  have hno : ∀ P : CompatibleLevelBarrier base π previous Flags EStar
      (fun n => (D n).region) (quotientNormalizedMap base.domainEquiv A.function) T.closedGate,
      ENNReal.ofReal T.selectionThreshold ≤ P.controlledSize := by
    intro P
    exact le_of_not_gt (fun h => hsmall ⟨P, h⟩)
  obtain ⟨L, htarget, _, hcontours, hgates⟩ := exists_gated_recursive_law_of_no_small_barrier
    hweighted hLusin hsard hsch base hU hG
    (by rw [hdust]; exact disjoint_compl_right) π hπ hclosed hsurj hr he
    (by rw [hdust]; exact hU.isClosed_compl) (by simpa only [hdust] using hTD)
    (by rw [hdust, compl_compl]) hdense hinfty
    (by simpa only [hdust] using hbad) hinf EStar hE hEU hEStar hEStarE hinfE
    (σ s) hpB D hnest hshrink hanchor (quotientNormalizedMap base.domainEquiv A.function)
    (quotientNormalizedMap_continuous base.domainEquiv A.function A.conformal.1)
    T.closedGate T.openGate T.closed_closedGate T.open_openGate T.closedGate_subset_openGate
    hfiber harcs previous hlevels hweightsFinite hpoint Flags hFlags
    (by simpa only [hdust] using hFlagsB) hmarked hunique' C₀ hC₀ hderiv
    hstandard hpath ω hω hωsum hdual hlift (ENNReal.ofReal T.selectionThreshold)
    (ENNReal.ofReal_pos.mpr T.selectionThreshold_pos) hno (fun _ => 0)
    (fun _ => inferInstance) (fun _ => by
      change (support (fun _ : Sphere => (0 : ℝ≥0∞))).Countable
      apply countable_empty.mono
      intro x hx
      exact (hx rfl).elim)
  let D' (n : ℕ) := (D n).retarget htarget
  have hregion (n : ℕ) : (D' n).region = (D n).region :=
    (D n).region_retarget htarget
  apply L.exists_selectable_protrusion_mean rank hrank hcoarea hsard hsch hsep
    base hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB
    C presentation hlevel hweights hmarked hsingular hP hunique ω
    hLusin hfiber harcs previous hprevious hweighted hcollar hselect Candidates label hflags hgraphs
    E T hq s hqs htarget (by simpa only [htarget] using hp) hseparated D'
    (by simpa only [hregion] using hnest)
    (by simpa only [hregion, htarget] using hshrink)
    (by simpa only [hregion] using hanchor)
    (by simpa only [hregion] using hfinite)
    (fun n => (congrFun hcontours n).trans (by rw [hregion]))
    (fun n => congrFun hgates n) B R hB hR hfar

end CircleDomainRigidity

end

end OAI
