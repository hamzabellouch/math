import OAI.Analysis.CircleDomains.Selection.ProtrusionTestAvailability
import OAI.Analysis.CircleDomains.Selection.ReanchoredExclusions
import OAI.Analysis.CircleDomains.Selection.RelevelledExclusions
import OAI.Analysis.CircleDomains.Selection.ProtrusionAnchors
import OAI.Analysis.CircleDomains.Selection.RankedSelectedLevels

namespace OAI

/-! The local construction is available against the whole preceding
ordered family. Its auxiliary anchor and level code are removed from the
returned test, preserving the original physical data and open exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_ordered_protrusion_test
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    {I : Type*} [LinearOrder I] [Countable I] (rank : ℕ ≃ I)
    (D : I → SelectableMaskedCoordinate base π)
    (pres : ∀ i, SelectedLevelPresentation hsch base π (D i).coordinate)
    (hcompat : ∀ (j : I) (n : ℕ) (labels : Fin n → I), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust) (p : B₀) (hpfinite : p.val.val ≠ OnePoint.infty)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (hq : q ∈ base.physicalDomainᶜ) (s : S) (hqs : π q = σ s) (hp : p.val.val = σ s)
    (hne : E.plane ≠ Metric.closedBall (A.center s) (A.radius s))
    (hB : B / 4 < M.radius)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J)) :
    ∃ T : CoordinateExclusionTest hsch base π B₀ (B / 4),
      T.mark = p ∧ T.coordinate.CompatibleWith (range D) ∧
      (p, (finiteSourceMap A.function (A.plane_open_embedding hG).1,
        A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈ T.neighborhood := by
  classical
  obtain ⟨T, hseparated⟩ := E.exists_local_test_geometry hG hr hq hqs hne
  obtain ⟨EStar, Anchor, hEstar, hAnchor, hEA, hAU, hE₀E, hinftyE, hzero⟩ :=
    T.exists_endpoint_anchors_retaining hU hπ base.domainEquiv he E₀ hE₀ hE₀U
  let code : PathCodeData Sphere Sphere :=
    { SelectableMaskedCoordinate.pathData (D ∘ rank) with anchor := Anchor }
  let H := code.levels
  let w := code.levelWeights
  let C (n : ℕ) := (D (rank n)).coordinate
  let previous : PriorLevelFamily code.physicalDomain π :=
    SelectableMaskedCoordinate.priorLevels (d := base) (D ∘ rank)
  let Flags : Set Sphere := ⋃ i, (D i).flags
  have hFlags : Flags.Countable := countable_iUnion (fun i => (D i).flags_countable)
  have hFlagsB : Flags ⊆ base.quotientDomainᶜ := by
    rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hdust ▸ (D i).flags_dust hi
  have hinfty : π OnePoint.infty ∉ base.dust := by
    rw [hdust, ← he ⟨_, hinf⟩]
    exact not_not.mpr (base.domainEquiv ⟨_, hinf⟩).property
  obtain ⟨collars, hnest, hshrink, hanchor, hfinite⟩ :=
    exists_anchored_shrinking_weighted_collars hweighted hsard hsch
      base.physicalDomain base.quotientDomain base.dust Anchor π hπ hclosed hsurj hr
      (by rw [hdust]; exact hU.isClosed_compl) (by simpa only [hdust] using hTD)
      (by rw [hdust]; exact disjoint_compl_right) (by simpa only [hdust] using hbad)
      hAnchor hAU hinfty (hp ▸ p.val.property) (hp ▸ hpfinite)
  let Candidates : Set (SelectableMaskedCoordinate code π) :=
    (fun c => c.withLevels H w) '' ((fun c => c.reanchor Anchor) '' range D)
  have hindex : ∀ c ∈ Candidates, ∃ n, c.coordinate.graph = previous.graph n := by
    rintro c ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨rank.symm i, ?_⟩
    change (D i).coordinate.graph = (D (rank (rank.symm i))).coordinate.graph
    rw [rank.apply_symm_apply]
  let label (c : SelectableMaskedCoordinate code π) : ℕ :=
    if hc : c ∈ Candidates then Classical.choose (hindex c hc) else 0
  have hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c) := by
    intro c hc
    dsimp only [label]
    rw [dite_eq_left hc]
    exact Classical.choose_spec (hindex c hc)
  have hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags := by
    rintro c ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩ x hx
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hmarked : ∀ n, support (code.levelWeights n) ⊆ Flags := by
    intro n x hx
    exact mem_iUnion.mpr ⟨rank n, (D (rank n)).weight_support hx⟩
  have hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ i a b,
      (a, x) ∈ code.levels i → (b, x) ∈ code.levels i → a = b := by
    intro x hx i a b ha hb
    apply (C i).unique_of_dustWeight_eq_zero (hdust.symm ▸ hx.1) _ ha hb
    by_contra hw
    exact hx.2 (hmarked i hw)
  have hP : RankedLevelNullCompatibility rank code.levels (base.quotientDomainᶜ \ Flags) := by
    simpa only [code, Flags, hdust] using selected_pathData_ranked_compatibility rank D hcompat
  obtain ⟨X, hXp, hXcomp, hXmem⟩ := exists_protrusion_exclusion_test rank rank.injective
    hcoarea hsard hsch hsep code hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad
    Flags hFlags hFlagsB C (fun n => (pres (rank n)).rebase (e := code) rfl rfl rfl)
    (fun _ => rfl) (fun _ => rfl) hmarked
    (fun n => mem_iUnion.mpr ⟨rank n, (D (rank n)).singular_marked⟩) hP hunique
    ω hω hωsum hLusin hfiber harcs previous (fun _ => rfl) hweighted hcollar hselect
    Candidates label hflags hgraphs E T hq s hqs hinf hseparated collars hnest hshrink
    hanchor hfinite EStar hAnchor hAU hEstar hEA
    (hEA (interior_subset hinftyE))
    (SelectableMaskedCoordinate.point_bound (D ∘ rank) (by rw [hdust, compl_compl]))
    C₀ hC₀ hderiv hstandard hpath hdual hlift B (10 * M.radius) hB
    (by linarith [M.radius_pos])
    (fun z hz => interior_subset (hEA (interior_subset (hE₀E (hfar z hz)))))
    harea hzero hconn hinftyE B₀ p hp
  let Y := X.withLevels base.levels base.levelWeights
  have hYcomp : Y.coordinate.CompatibleWith ((fun c => c.reanchor Anchor) '' range D) :=
    X.withLevels_compatible (base := {base with anchor := Anchor}) hXcomp
  let Z : CoordinateExclusionTest hsch base π B₀ (B / 4) := Y.reanchor base.anchor
  refine ⟨Z, hXp, Y.reanchor_compatible (base := base) hYcomp, ?_⟩
  have hZY : Z.neighborhood = Y.neighborhood := Y.neighborhood_reanchor base.anchor
  have hYX : Y.neighborhood = X.neighborhood :=
    X.neighborhood_withLevels base.levels base.levelWeights
  exact hZY.symm ▸ (hYX.symm ▸ hXmem)

end CircleDomainRigidity

end

end OAI
