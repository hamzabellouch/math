import OAI.Geometry.CylinderCovering.Footprints.ShapesDefinitions

namespace OAI

noncomputable section

namespace CylinderCovering.Footprints

def radialReflection : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (-p.1, p.2)
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' a p := by ext <;> simp

def positiveAbsoluteVertices (m M d A B : ℝ) : Fin 4 → ℝ × ℝ :=
  trapezoidVertices m (M + A * d) d 0 B

def negativeAbsoluteVertices (m d A B : ℝ) : Fin 4 → ℝ × ℝ :=
  radialReflection ∘ trapezoidVertices (-m) (A * d) d 0 B

def AbsolutePolygonStatement : Prop :=
  ∀ m M d A B : ℝ, 0 ≤ M → 0 < d → 0 < A → 0 < B →
    absoluteFootprint m M d A B =
      convexHull ℝ (Set.range (positiveAbsoluteVertices m M d A B)) ∪
      convexHull ℝ (Set.range (negativeAbsoluteVertices m d A B)) ∧
    Function.Injective (positiveAbsoluteVertices m M d A B) ∧
    Function.Injective (negativeAbsoluteVertices m d A B)

end CylinderCovering.Footprints

end

end OAI
