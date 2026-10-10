import OAI.Geometry.EinsteinFour.MetricDoubleCover
import OAI.Geometry.EinsteinFour.FrameOrientation
import Mathlib.Geometry.Manifold.Category.MfldCat.OfModel

namespace OAI

/-! The topological reduction from the oriented two-model theorem to the
unoriented three-model theorem uses the orientation cover, its pullback metric
and the Euler/Betti identities from Hatcher. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

universe u

/-- A closed connected oriented Riemannian four-manifold, with its genuine
smooth manifold structure. The measurable structure can be installed as
the Borel structure when applying the analytic theorem. -/
structure ClosedOrientedMetricFour where
  manifold : ModelWithCorners.MfldCat.{u} I4 ∞
  [regular : T3Space manifold]
  [secondCountable : SecondCountableTopology manifold]
  [compact : CompactSpace manifold]
  [connected : ConnectedSpace manifold]
  metric : SmoothMetric manifold
  orientation : Geometry.FrameOrientation metric

attribute [instance] ClosedOrientedMetricFour.regular
  ClosedOrientedMetricFour.secondCountable ClosedOrientedMetricFour.compact
  ClosedOrientedMetricFour.connected

variable {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Hatcher's connected orientation cover, equipped with the pullback
metric. Preservation of Einstein and positive sectional curvature is the
local-isometry specialization in Petersen §1.3.3. -/
structure OrientationMetricDoubleCover (g : SmoothMetric M) where
  oriented : ClosedOrientedMetricFour.{u}
  cover : MetricDoubleCover g oriented.metric
  einstein : IsEinstein g → IsEinstein oriented.metric
  positive : HasPositiveSectionalCurvature g → HasPositiveSectionalCurvature oriented.metric

/-- Hatcher, Proposition 3.25 and Theorem 3.26(c), together with smooth
metric pullback: either an orientation exists, or its connected two-sheeted
cover has the displayed actual geometric data. -/
def HatcherOrientationCoverInput (g : SmoothMetric M) : Prop :=
  Nonempty (Geometry.FrameOrientation g) ∨ Nonempty (OrientationMetricDoubleCover g)

/-- The precise covering/topological inputs needed after the oriented
classification. The Euler and Betti statements concern the actual cover
manifold; the antipodal quotient is proved from its metric data. -/
structure UnorientedPublishedInputs (g : SmoothMetric M) : Prop where
  orientationCover : HatcherOrientationCoverInput g
  euler : ∀ C : OrientationMetricDoubleCover g,
    HatcherDoubleEulerInput (M := M) (N := C.oriented.manifold)
  projectiveBetti : ∀ C : OrientationMetricDoubleCover g,
    HatcherProjectiveBettiInput C.oriented.metric

variable [T3Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]

/-- The oriented analytic classification, once supplied for every closed
oriented metric, implies the full unoriented classification. The sphere
cover descends through a proved free-involution quotient; the CP² cover
contradicts the proved odd Euler obstruction. -/
theorem classified_of_oriented_models (g : SmoothMetric M)
    (hpublished : UnorientedPublishedInputs g)
    (hmodels : ∀ X : ClosedOrientedMetricFour.{u},
      IsEinstein X.metric → HasPositiveSectionalCurvature X.metric →
        ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo X.metric a roundDistance ∨
          ScaledIsometricTo X.metric a fubiniStudyDistance))
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    Classified g := by
  rcases hpublished.orientationCover with ho | hC
  · obtain ⟨o⟩ := ho
    let X : ClosedOrientedMetricFour.{u} :=
      { manifold := ModelWithCorners.MfldCat.of M
        metric := g
        orientation := o }
    obtain ⟨a, ha, hs | hp⟩ := hmodels X hEinstein hpositive
    · exact ⟨a, ha, Or.inl hs⟩
    · exact ⟨a, ha, Or.inr (Or.inl hp)⟩
  · obtain ⟨C⟩ := hC
    exact C.cover.classified_of_two_models (hpublished.euler C)
      (hpublished.projectiveBetti C)
      (hmodels C.oriented (C.einstein hEinstein) (C.positive hpositive))

end
end PositiveEinsteinFour

end OAI
