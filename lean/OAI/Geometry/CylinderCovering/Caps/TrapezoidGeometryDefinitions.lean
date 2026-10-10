import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace CylinderCovering.HalfheightFinite

def NondegenerateTrapezoid (B : Set Space) : Prop :=
  ∃ v : Fin 4 → Space,
    B = convexHull ℝ (range v) ∧ Function.Injective v ∧
    AffineIndependent ℝ ![v 0, v 1, v 2] ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ w : Space, w ≠ 0 ∧
      v 1 - v 0 = a • w ∧ v 3 - v 2 = b • w

structure GeometryStatement : Prop where
  unitEdge : ∃ v : Fin 4 → Space, AffineIndependent ℝ v ∧
    (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = 1) ∧
    tetrahedron = convexHull ℝ (range v)
  minimumShadow : Similarity.minimumArea tetrahedron = height / 2
  sourceTrapezoids : ∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∀ i : Fin N,
    NondegenerateTrapezoid (firstBase δ (cubicCap δ) N i) ∧
    NondegenerateTrapezoid (secondBase δ (cubicCap δ) N i) ∧
    NondegenerateTrapezoid (firstBase δ (fractionalCap δ) N i) ∧
    NondegenerateTrapezoid (secondBase δ (fractionalCap δ) N i)
  eventualHalfMinimum : ∀ᶠ δ : ℝ in 𝓝[>] 0,
    (∀ᶠ N in atTop, 0 < N ∧
      totalArea δ (cubicCap δ) N < Similarity.minimumArea tetrahedron / 2) ∧
    (∀ᶠ N in atTop, 0 < N ∧
      totalArea δ (fractionalCap δ) N < Similarity.minimumArea tetrahedron / 2)

end CylinderCovering.HalfheightFinite

end

end OAI
