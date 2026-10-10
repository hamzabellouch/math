import OAI.Geometry.CylinderCovering.Simplex.ProjectionDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering

def RegularMetricNormalizationStatement : Prop :=
  ∀ v : Fin 4 → Space, AffineIndependent ℝ v →
    ∀ edge : ℝ, 0 < edge →
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) →
      Metric.diam (convexHull ℝ (range v)) = edge ∧
      volume.real (convexHull ℝ (range v)) = edge ^ 3 / (6 * Real.sqrt 2) ∧
      minimumShadowArea (convexHull ℝ (range v)) / 2 = edge ^ 2 / (4 * Real.sqrt 2)

end CylinderCovering

end

end OAI
