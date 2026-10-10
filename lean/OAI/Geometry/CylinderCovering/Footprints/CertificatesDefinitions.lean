import OAI.Geometry.CylinderCovering.Footprints.ShapesDefinitions
import OAI.Geometry.CylinderCovering.Radial.TriangleDefinitions

namespace OAI

namespace CylinderCovering.Footprints
open MeasureTheory Set

structure LocalFootprintCertificates : Prop where
  intercept_identity : ∀ ε x q c ρ : ℝ,
    (quadraticIntercept ε x q c ρ).2 - c * (quadraticIntercept ε x q c ρ).1 =
      (q - c) * ρ - ε * x / 2 * (q - c)^2
  arbitrary_absolute : ∀ ε x q c ρ m M d A B : ℝ,
    0 ≤ ε → 0 ≤ d → |x| ≤ 2 → |q-c| ≤ d → |q-m| ≤ d/2 →
    0 ≤ ρ → ρ ≤ M → 2*ε ≤ A → ε ≤ B →
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint m M d A B
  midpoint_absolute : ∀ ε x q c ρ M d A B : ℝ,
    0 ≤ ε → 0 ≤ d → |x| ≤ 2 → |q-c| ≤ d/2 →
    0 ≤ ρ → ρ ≤ M → ε ≤ A → ε/4 ≤ B →
    quadraticIntercept ε x q c ρ ∈ absoluteFootprint c M d A B
  midpoint_affine : ∀ ε x q c ρ M d A B : ℝ,
    0 ≤ ε → 0 ≤ d → |x| ≤ 2 → |q-c| ≤ d/2 →
    0 ≤ ρ → ρ ≤ M → ε ≤ A → 3*ε/4 ≤ B →
    quadraticIntercept ε x q c ρ ∈ affineFootprint c M d A B
  endpoint_affine : ∀ ε x q c ρ M d : ℝ,
    0 ≤ ε → 0 ≤ d → |x| ≤ 2 → 0 ≤ q-c → q-c ≤ d → 0 ≤ ρ → ρ ≤ M →
    quadraticIntercept ε x q c ρ ∈ endpointFootprint c M d ε
  absolute_area : ∀ m M d A B : ℝ, 0 ≤ M → 0 ≤ d → 0 ≤ A → 0 ≤ B →
    volume.real (absoluteFootprint m M d A B) = absoluteArea M d A B
  affine_area : ∀ m M d A B : ℝ, 0 ≤ M → 0 ≤ d → 0 ≤ A → A/2 ≤ B →
    volume.real (affineFootprint m M d A B) = affineArea M d A B
  absolute_compact : ∀ m M d A B : ℝ, IsCompact (absoluteFootprint m M d A B)
  affine_compact : ∀ m M d A B : ℝ, IsCompact (affineFootprint m M d A B)
  affine_convex : ∀ m M d A B : ℝ, Convex ℝ (affineFootprint m M d A B)
  absolute_not_convex : ∀ m M d A B : ℝ,
    0 ≤ M → 0 < d → 0 < A → 0 ≤ B → ¬ Convex ℝ (absoluteFootprint m M d A B)
  endpoint_identity : ∀ c M d ε : ℝ,
    endpointFootprint c M d ε = affineFootprint (c+d/2) M d (2*ε) (3*ε)
  triangle_hull : ∀ m M d A : ℝ, 0 < d → 0 < M+2*A*d →
    affineFootprint m M d A (A/2) =
      convexHull ℝ (range (RadialTriangle.vertices (-A*d) (M+A*d) m d))
  triangle_independent : ∀ m M d A : ℝ, 0 < d → 0 < M+2*A*d →
    AffineIndependent ℝ (RadialTriangle.vertices (-A*d) (M+A*d) m d)
  trapezoid_hull : ∀ m M d A B : ℝ, 0 < d → A/2 < B → 0 < M+2*A*d →
    affineFootprint m M d A B = convexHull ℝ (range (trapezoidVertices m M d A B))
  trapezoid_distinct : ∀ m M d A B : ℝ, 0 < d → A/2 < B → 0 < M+2*A*d →
    Function.Injective (trapezoidVertices m M d A B)
  trapezoid_sides : ∀ m M d A B : ℝ,
    trapezoidVertices m M d A B 1 - trapezoidVertices m M d A B 0 =
      (0, 2*(d/2*(-A*d)+B*d^2)) ∧
    trapezoidVertices m M d A B 3 - trapezoidVertices m M d A B 2 =
      (0, 2*(d/2*(M+A*d)+B*d^2))
  midpoint_inclusion : ∀ c M d ε : ℝ, 0 ≤ d → 0 ≤ ε →
    affineFootprint c M d ε (3*ε/4) ⊆ absoluteFootprint c M d ε ε
  midpoint_finite_difference : ∀ M d ε : ℝ,
    absoluteArea M d ε ε - affineArea M d ε (3*ε/4) = ε/2*M*d^2+2*ε^2*d^3

end CylinderCovering.Footprints

end OAI
