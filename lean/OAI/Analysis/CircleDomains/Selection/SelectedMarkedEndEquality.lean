import OAI.Analysis.CircleDomains.Selection.OrderedProtrusionAvailability
import OAI.Analysis.CircleDomains.Selection.SelectedExclusionUnion
import OAI.Analysis.CircleDomains.Selection.FullSelectedCompatibility

namespace OAI

/-! Coverage and the constructed local test rule out every protrusion at
a mandatory marked end of the actual selected mixed limit. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem selected_marked_end_eq_disk
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
    ∀ (p : B₀) (x : Sphere), x ∈ base.physicalDomainᶜ → π x = p.val.val →
      ∀ E : RealTargetEnd A.toReal x,
        E.plane = Metric.closedBall (A.center ⟨p.val, F.mandatory p.property⟩)
          (A.radius ⟨p.val, F.mandatory p.property⟩) := by
  classical
  let : Countable (ℕ ⊕ₗ ℕ) := Function.Injective.countable
    (show Injective (ofLex : (ℕ ⊕ₗ ℕ) → ℕ ⊕ ℕ) from fun _ _ h => by
      simpa only [toLex_ofLex] using congrArg toLex h)
  intro p x hx hxp E
  by_contra hne
  have hpfinite : p.val.val ≠ OnePoint.infty := by
    intro hp
    have hd : p.val.val ∈ base.quotientDomainᶜ := hdust ▸ p.val.property
    exact hd (hp ▸ hinftyU)
  obtain ⟨T, _, hT, hmem⟩ := exists_ordered_protrusion_test hcoarea hweighted hLusin
    hsard hsch hsep hcollar hselect harea base hG hconn hU hdense hdust π hπ hclosed
    hsurj hr he hTD hbad hinf hfiber harcs selectedCoordinateEnumeration
    (orderedSelectedCoordinates seed CoordinateExclusionTest.coordinate q)
    (orderedSelectedPresentations seed seedPresentation CoordinateExclusionTest.coordinate
      CoordinateExclusionTest.presentation q) hcompat E₀ hE₀ hE₀U B hfar B₀ p hpfinite
    E hx ⟨p.val, F.mandatory p.property⟩ hxp rfl hne hB C₀ hC₀ hderiv hstandard hpath
    ω hω hωsum hdual hlift
  exact selected_limit_avoids_test_union seed seedPresentation S q hpref F A
    hgreen harea hG hinf hπ hclosed p
    (hcover T (seeded_allowed_of_ordered_compatible seed CoordinateExclusionTest.coordinate
      S q hpref T hT) hmem)

end CircleDomainRigidity

end

end OAI
