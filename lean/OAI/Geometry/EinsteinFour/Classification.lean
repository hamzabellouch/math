import OAI.Geometry.EinsteinFour.ActualModelIdentification

namespace OAI

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

/-- Every closed connected Einstein four-manifold with strictly positive sectional
curvature is isometric, after positive scaling, to the round sphere, complex
projective plane, or real projective four-space. -/
theorem classification (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] (g : SmoothMetric M)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo g a roundDistance ∨
        ScaledIsometricTo g a fubiniStudyDistance ∨
        ScaledIsometricTo g a realProjectiveDistance) :=
  classificationOn M g hEinstein hpositive

end PositiveEinsteinFour

end OAI
