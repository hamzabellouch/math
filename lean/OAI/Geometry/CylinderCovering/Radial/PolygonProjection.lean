import OAI.Geometry.CylinderCovering.Footprints.Polygon
import OAI.Geometry.CylinderCovering.Radial.ProjectionShapes

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace RadialProjection
open TriangularCovering CylinderCovering.Footprints

theorem projected_absolute_polygon (p₀ : Space) {e w a b : Space}
    (he : ‖e‖ = 1) (hw : inner ℝ e w = 0)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hab : LinearIndependent ℝ (![a,b] : Fin 2 → Space))
    {m M d A B : ℝ} (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    let f := projectedCoordinateAffine (unit (e+w)) p₀ a b
    f '' absoluteFootprint m M d A B =
        convexHull ℝ (range (f ∘ positiveAbsoluteVertices m M d A B)) ∪
        convexHull ℝ (range (f ∘ negativeAbsoluteVertices m d A B)) ∧
      Function.Injective (f ∘ positiveAbsoluteVertices m M d A B) ∧
      Function.Injective (f ∘ negativeAbsoluteVertices m d A B) ∧
      ¬ Convex ℝ (f '' absoluteFootprint m M d A B) := by
  dsimp only
  have hf := projectedCoordinateAffine_injective p₀ he hw ha hb hab
  refine ⟨absoluteFootprint_image_eq_union_hulls _ hM hd hA hB,
    hf.comp (positiveAbsoluteVertices_injective hM hd hA hB),
    hf.comp (negativeAbsoluteVertices_injective hd hA hB), ?_⟩
  intro hconv
  exact (absoluteFootprint_not_convex hM hd hA hB.le)
    ((projectedCoordinateAffine_convex_iff p₀ he hw ha hb hab _).mp hconv)

end RadialProjection

end

end OAI
