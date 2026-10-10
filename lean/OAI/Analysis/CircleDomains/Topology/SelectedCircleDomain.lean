import OAI.Analysis.CircleDomains.Selection.SelectedMarkedEndEquality
import OAI.Analysis.CircleDomains.Transfer.RetainedSmallTests
import OAI.Analysis.CircleDomains.Selection.SelectedRealCollapse
import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks
import OAI.Analysis.CircleDomains.Transfer.RoundOuterCore

namespace OAI

/-! The selected mixed limit is a circle domain: its mandatory ends are the
exact selected disks, and the original graded real tests collapse all other ends. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem selected_limit_isCircleDomain
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ) (hinftyU : OnePoint.infty ∈ base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hBimage : base.dust = π '' base.physicalDomainᶜ)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (S : ℕ → Set (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (q : ℕ → Option (CoordinateExclusionTest hsch base π B₀ (B / 4)))
    (hpref : ∀ n c, c ∈ S n ↔ ∃ k < n, q k = some c)
    (hcover : ∀ t, seededMaskedAllowed seed CoordinateExclusionTest.coordinate (⋃ n, S n) t →
      t.neighborhood ⊆ ⋃ t ∈ ⋃ n, S n, t.neighborhood)
    (hcompat : let D := orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q
      ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
            (fun k => (D k).coordinate.graph) labels) = 0)
    (F : SelectedMixedModels hsch base hU hdense π he hBimage
      (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
      (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q) B₀)
    (A : AssignedMixedModelLimit F.model) (hB : B / 4 < F.model.real.radius)
    (hBouter : B ≤ 2 * F.model.real.radius)
    (tests : Set (GradedRealTest base π E₀))
    (hretained : ∀ b ∈ tests, ∃ (i : ℕ), (seedPresentation i).coordinate = b.coordinate)
    (htests : ∀ p ∈ base.dust \ (Subtype.val '' B₀),
      ∀ k, ∃ b ∈ tests, b.grade = k ∧ p ∈ b.region)
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
    IsCircleDomain (extendAtInfinity A.function '' base.physicalDomain) := by
  classical
  refine ⟨A.conformal.1.isOpen_image hG hG (Subset.refl _),
    hconn.image _ (fun z hz => (A.conformal.1 z hz).1.continuousWithinAt), ?_⟩
  intro p hp
  obtain ⟨x, hx, E, hE⟩ := A.toReal.exists_source_end hG hp
  have hpx : π x ∈ base.dust := hBimage ▸ ⟨x, hx, rfl⟩
  by_cases hm : π x ∈ Subtype.val '' B₀
  · obtain ⟨b, hb, hbx⟩ := hm
    let b₀ : B₀ := ⟨b, hb⟩
    have hdisk := selected_marked_end_eq_disk hcoarea hweighted hLusin hsard hsch hsep hcollar hselect hgreen harea base hG hconn hU hdense hdust hinftyU
      π hπ hclosed hsurj hr he hTD hbad hinf hBimage hfiber harcs E₀ hE₀ hE₀U
      B hfar B₀ seed seedPresentation S q hpref hcover hcompat F A hB C₀ hC₀ hderiv
      hstandard hpath ω hω hωsum hdual hlift b₀ x hx hbx.symm E
    have hsphere := E.sphere_image_plane
    rw [hdisk, hE] at hsphere
    change ((↑) : ℂ → Sphere) '' Metric.closedBall
      (A.center ⟨b₀.val, F.mandatory b₀.property⟩) (A.radius ⟨b₀.val, F.mandatory b₀.property⟩) =
        connectedComponentIn (extendAtInfinity A.function '' base.physicalDomain)ᶜ p at hsphere
    exact hsphere ▸ coe_closedBall_is_singleton_or_round _ (A.bounds _).2.1
  · have hsmall : SmallAnchoredPlateaus F.realCoordinates E₀ (π x) := by
      apply F.small_anchored_of_retained_tests_at E₀ tests ?_ (π x) (htests _ ⟨hpx, hm⟩)
      intro b hb
      obtain ⟨i, hi⟩ := hretained b hb
      exact ⟨Sum.inlₗ i, seedPresentation i,
        orderedSelectedPresentations_seed seed seedPresentation
          CoordinateExclusionTest.coordinate CoordinateExclusionTest.presentation q i, hi⟩
    have hzero : ∀ z ∈ frontier (jordanInterior (F.model.real.outerCore.disk 0)),
        π (z : Sphere) ∈ E₀ := by
      rw [F.model.real.outerCore_interior,
        frontier_ball _ (ne_of_gt (mul_pos (by norm_num) F.model.real.radius_pos))]
      intro z hz
      apply hfar
      have hn : ‖z‖ = 2 * F.model.real.radius := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      exact hn ▸ hBouter
    have hc := E.target_eq_singleton_of_small_anchored_coordinates hsard hsch harea
      hG hconn modelError_tendsto hπ hr hx F.model.real.outerCore 0
      (F.model.real.component_inside_outerCore x) E₀ hzero hsmall
    change connectedComponentIn (extendAtInfinity A.function '' base.physicalDomain)ᶜ
      E.point = {E.point} at hc
    exact Or.inl ⟨p, hE ▸ hc⟩

end CircleDomainRigidity

end

end OAI
