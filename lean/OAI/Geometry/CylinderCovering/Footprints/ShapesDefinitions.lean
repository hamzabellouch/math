import OAI.Geometry.CylinderCovering.Footprints.QuadraticFootprintsDefinitions
import OAI.Geometry.CylinderCovering.Radial.TriangleDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Footprints

def trapezoidVertices (m M d A B : ℝ) : Fin 4 → ℝ × ℝ :=
  let l := -A*d
  let r := M+A*d
  ![(l,m*l-(d/2*l+B*d^2)), (l,m*l+(d/2*l+B*d^2)),
    (r,m*r-(d/2*r+B*d^2)), (r,m*r+(d/2*r+B*d^2))]

def ShapeStatement : Prop :=
  (∀ m M d A B : ℝ, 0 ≤ M → 0 < d → 0 < A → 0 ≤ B →
    ¬ Convex ℝ (absoluteFootprint m M d A B)) ∧
  (∀ m M d A : ℝ, 0 < d → 0 < M+2*A*d →
    affineFootprint m M d A (A/2) =
      convexHull ℝ (Set.range (RadialTriangle.vertices (-A*d) (M+A*d) m d)) ∧
    AffineIndependent ℝ (RadialTriangle.vertices (-A*d) (M+A*d) m d)) ∧
  (∀ m M d A B : ℝ, 0 < d → A/2 < B → 0 < M+2*A*d →
    affineFootprint m M d A B = convexHull ℝ (Set.range (trapezoidVertices m M d A B)) ∧
    Function.Injective (trapezoidVertices m M d A B) ∧
    trapezoidVertices m M d A B 1 - trapezoidVertices m M d A B 0 =
      (0,2*(d/2*(-A*d)+B*d^2)) ∧
    trapezoidVertices m M d A B 3 - trapezoidVertices m M d A B 2 =
      (0,2*(d/2*(M+A*d)+B*d^2))) ∧
  (∀ m M d A B : ℝ, 0 ≤ M → 0 < d → 0 ≤ A → A/2 < B →
    0 < M+2*A*d → (interior (affineFootprint m M d A B)).Nonempty)

end CylinderCovering.Footprints

end

end OAI
