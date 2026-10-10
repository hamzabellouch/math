import OAI.Geometry.Manifold.ProjectiveSphere

namespace OAI

/-!
# The classification target

The classification identifies a positively curved Einstein metric, after
positive rescaling, with one of the three standard model distances.
-/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The three metric models in the manuscript's unoriented classification.
`a` is the positive factor multiplying the original Riemannian metric. -/
def Classified (g : SmoothMetric M) : Prop :=
  ∃ a : ℝ, 0 < a ∧
    (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance ∨
      ScaledIsometricTo g a realProjectiveDistance)

/-- The family of main claims for a fixed smooth four-manifold. Compactness
encodes "closed" since the model has no boundary. -/
def ClassificationOn (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [ConnectedSpace M] : Prop :=
  ∀ g : SmoothMetric M,
    IsEinstein g → HasPositiveSectionalCurvature g → Classified g

end PositiveEinsteinFour

end OAI
