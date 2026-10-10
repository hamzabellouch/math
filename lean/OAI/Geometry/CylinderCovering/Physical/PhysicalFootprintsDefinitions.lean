import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.PhysicalFootprints
open RuledApproximation

def footCoordinates (q : ℝ × ℝ) : Plane := vec2 q.2 (1 - q.1)

def physicalFoot (h : ℝ) (q : ℝ × ℝ) : Space :=
  vec3 0 q.2 (h * (1 - q.1))

def direction (h : ℝ) (g : Plane) : Space := vec3 1 (g 0) (h * g 1)

def unitDirection (h : ℝ) (g : Plane) : Space :=
  ‖direction h g‖⁻¹ • direction h g

def projectedFoot (h : ℝ) (g : Plane) (q : ℝ × ℝ) : Space :=
  physicalFoot h q -
    (inner ℝ (direction h g) (physicalFoot h q) / ‖direction h g‖ ^ 2) •
      direction h g

def sweptFootprint (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) : Set Space :=
  {x | ∃ q ∈ F, ∃ s : ℝ, x = physicalFoot h q + s • direction h g}

def PhysicalStatement : Prop :=
  ∀ (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)), 0 < h → IsCompact F →
    Function.Injective (projectedFoot h g) ∧
    ∃ C : Cylinder,
      C.axis = unitDirection h g ∧
      Subtype.val '' C.base = projectedFoot h g '' F ∧
      IsCompact C.base ∧ MeasurableSet C.base ∧ volume C.base < ⊤ ∧
      C.carrier = sweptFootprint h g F ∧
      C.area = h * volume.real F * physicalWeight h g

def ProjectionShapeStatement : Prop :=
  ∀ (h : ℝ) (g : Plane), 0 < h →
    (∀ F : Set (ℝ × ℝ),
      Convex ℝ (projectedFoot h g '' F) ↔ Convex ℝ F) ∧
    (∀ (n : ℕ) (p : Fin n → ℝ × ℝ),
      AffineIndependent ℝ (projectedFoot h g ∘ p) ↔ AffineIndependent ℝ p) ∧
    (∀ F : Set (ℝ × ℝ),
      projectedFoot h g '' convexHull ℝ F = convexHull ℝ (projectedFoot h g '' F))

end CylinderCovering.PhysicalFootprints

end

end OAI
