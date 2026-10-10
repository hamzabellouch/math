import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Topology.SelectedCircleDomain
import OAI.Analysis.CircleDomains.Selection.SelectedMixedSelection
import OAI.Analysis.CircleDomains.Selection.PresentedRealSeed
import OAI.Analysis.CircleDomains.Uniformization.Conformal
import OAI.Analysis.CircleDomains.Selection.CountableSmallRealTests
import OAI.Analysis.CircleDomains.Selection.SeededSmallRealTests

namespace OAI

/-! Assemble the actual graded real seed, countable open exclusion selection,
common mixed models and their normal limit into a circle uniformization. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

open FiniteTransfer

/-- A circle-domain normal limit with the original finite scalar list retained
on the actual finite-transfer exhaustion. Sobolev continuation of its traces
is a separate conclusion proved from these data. -/
structure RetainedRealCircleModel (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    {m : ℕ} (Q : Fin m → PhysicalRealCoordinate base π) where
  marks : Set base.dust
  marks_countable : marks.Countable
  coordinates : CountableRealCoordinates base.physicalDomain π (fun s : marks => s.val.val)
  source : coordinates.source = base.quotientDomain
  model : RealModelExhaustion coordinates
    (markedNeighborhoods (fun s : marks => s.val.val)) modelError
  limit : AssignedRealModelLimit model
  circle : IsCircleDomain (extendAtInfinity limit.function '' base.physicalDomain)
  index : Fin m → ℕ
  physical : ∀ i, coordinates.physical (index i) = (Q i).physical
  quotient : ∀ i, coordinates.coordinate (index i) = (Q i).quotient

theorem exists_retained_real_circle_model
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hconn : IsConnected d.physicalDomain) (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hdust : d.dust = d.quotientDomainᶜ) (hne : d.dust.Nonempty)
    (hinftyU : OnePoint.infty ∈ d.quotientDomain)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (hinfStar : π OnePoint.infty ∈ interior EStar)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ EStar)
    (hBimage : d.dust = π '' d.physicalDomainᶜ)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : d.dust, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : d.dust, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)] (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
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
    {m : ℕ} (T : Fin (m + 1) → UngatedRealTest d π EStar)
    (hT0 : T 0 = UngatedRealTest.zeroTest d π EStar)
    (hT : ∀ (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1)),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (T i).exclusions)
          (circleBandGraph d.quotientDomain (T j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (T i).coordinate.quotient) labels) = 0)
    : Nonempty (RetainedRealCircleModel d π (fun i => (T i).coordinate)) := by
  classical
  obtain ⟨tests, c, N, hNc, hNB, hc0, hprefix, _, hselected, hcompat, htests⟩ :=
    exists_countable_small_real_tests_with_seed hcross hcoarea hLusin hsard hsch d hU hG hdisj
      π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar
      hEStarE hinfE hBimage D hnest hshrink hED hfiber harcs C hC hderiv hstandard hpath
      ω hω hωsum hdual hlift T hT0 hT
  obtain ⟨p, hp⟩ := hne
  obtain ⟨seed, _, hseed0, hseed, P, hP⟩ := exists_presented_real_seed hcoarea d hU hG hdense
    π hπ he hBimage ⟨p, hp⟩ EStar hinfStar c
    (by rw [hc0]; rfl) N hNc hNB hcompat
  let B₀ : Set d.dust := Subtype.val ⁻¹' N
  have hB₀ : B₀.Countable := hNc.preimage Subtype.val_injective
  let : Countable B₀ := hB₀.to_subtype
  let : TopologicalSpace B₀ := ⊥
  let : DiscreteTopology B₀ := ⟨rfl⟩
  let : SecondCountableTopology (MapDiskData d.physicalDomain) := mapDiskData_secondCountable hG
  obtain ⟨S, q, _, _, _, _, _, hpref, hcover, hordered, ⟨F⟩⟩ :=
    exists_selected_mixed_selection hsard hsch hcompact hfinite d hU hG hconn hinf
      hdense π hπ hclosed hsurj hr he hBimage hTD hdisj seed P hseed0 hseed
      (T := CoordinateExclusionTest hsch d π B₀ (B / 4))
      CoordinateExclusionTest.coordinate CoordinateExclusionTest.presentation
      CoordinateExclusionTest.neighborhood (fun t => t.isOpen_neighborhood) B₀ hB₀
  let R := max F.model.real.radius (max (B / 4 + 1) (B / 2))
  let F' := F.withRadius R (le_max_left _ _)
  have hBR : B / 4 < F'.model.real.radius := by
    change B / 4 < R
    exact lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans (le_max_right _ _))
  have hB2 : B ≤ 2 * F'.model.real.radius := by
    change B ≤ 2 * R
    have h : B / 2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  let : Countable F'.marks := F'.marks_countable.to_subtype
  obtain ⟨A⟩ := F'.model.exists_assigned_limit harea hmontel hhurwitz hzero
    hsard hsch hG hconn
  have hcircle : IsCircleDomain (extendAtInfinity A.function '' d.physicalDomain) := by
    refine selected_limit_isCircleDomain hplane hcoarea hLusin hsard hsch hsep hcollar
      hselect hgreen harea d hG hconn hU hdense hdust hinftyU π hπ hclosed hsurj hr he (hdust ▸ hTD) (fun p hp => hdust ▸ hbad p hp)
      hinf hBimage hfiber harcs EStar hEStar (hEStarE.trans (interior_subset.trans hEU))
      B hfar B₀ seed P S q hpref hcover hordered F' A hBR hB2 tests ?_ ?_
      C hC hderiv hstandard hpath ω hω hωsum hdual hlift
    · intro b hb
      obtain ⟨i, hi⟩ := hselected b hb
      exact ⟨i, (hP i).trans (congrArg UngatedRealTest.coordinate hi)⟩
    · intro p hp k
      apply htests p ⟨hp.1, ?_⟩ k
      intro hpN
      apply hp.2
      exact ⟨⟨p, hp.1⟩, hpN, rfl⟩
  have hretained (i : Fin (m + 1)) : ∃ j,
      F'.realCoordinates.physical j = (T i).coordinate.physical ∧
      F'.realCoordinates.coordinate j = (T i).coordinate.quotient := by
    obtain ⟨j, _, hp, hq⟩ := F'.retains_real_presentation (Sum.inlₗ i.val) (P i.val)
      (orderedSelectedPresentations_seed seed P CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q i.val)
    have hQ : (P i.val).coordinate = (T i).coordinate :=
      (hP i.val).trans (congrArg UngatedRealTest.coordinate (hprefix i))
    exact ⟨j, hp.trans (congrArg PhysicalRealCoordinate.physical hQ),
      hq.trans (congrArg PhysicalRealCoordinate.quotient hQ)⟩
  choose idx hphysical hquotient using hretained
  exact ⟨{
    marks := F'.marks
    marks_countable := F'.marks_countable
    coordinates := F'.realCoordinates
    source := rfl
    model := F'.model.real
    limit := A.toReal
    circle := hcircle
    index := idx
    physical := hphysical
    quotient := hquotient }⟩

end CircleDomainRigidity

end

end OAI
