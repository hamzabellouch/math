import OAI.Geometry.CylinderCovering.Rational.SimilarityDefinitions
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
namespace RationalSimilarity

def uncenteredVertices : Fin 4 → Space :=
  ![!₂[Real.sqrt 2, 0, 0], !₂[-Real.sqrt 2, 0, 0],
    !₂[0, Real.sqrt 2, 2], !₂[0, -Real.sqrt 2, 2]]

def UncenteredTetrahedronGeometryStatement : Prop :=
  AffineIndependent ℝ uncenteredVertices ∧
  (∀ i j : Fin 4, i ≠ j →
    dist (uncenteredVertices i) (uncenteredVertices j) = 2 * Real.sqrt 2) ∧
  uncenteredTetrahedron = convexHull ℝ (Set.range uncenteredVertices) ∧
  CylinderCovering.IsRegularTetrahedron uncenteredTetrahedron ∧
  Metric.diam uncenteredTetrahedron = 2 * Real.sqrt 2 ∧
  MeasureTheory.volume.real uncenteredTetrahedron = 8 / 3 ∧
  CylinderCovering.minimumShadowArea uncenteredTetrahedron = 2 * Real.sqrt 2

end RationalSimilarity

end

end OAI
