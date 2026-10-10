import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions

namespace OAI

namespace SlopeRational

noncomputable section

def inverseRectangle (d : ℝ) : Set Plane :=
  {z | |z 0| ≤ 1 ∧ -1 ≤ z 1 ∧ z 1 ≤ 1 / 2 + d / 2}

def tiltedMap (d s : ℝ) (z : Plane) : Plane := z + s • field d z

def RectangleInversionAt (d : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
    (∀ y t : ℝ, |y| ≤ 1 / 2 → |t| ≤ 1 / 2 →
      ∃! p : Plane, p ∈ inverseRectangle d ∧ tiltedMap d s p = vec2 y t) ∧
    (∀ p ∈ inverseRectangle d, ∀ q ∈ inverseRectangle d,
      (tiltedMap d s p) 0 = (tiltedMap d s q) 0 →
      (tiltedMap d s p) 1 < (tiltedMap d s q) 1 → p 1 < q 1)

def RectangleInversionStatement : Prop :=
  ∀ d : ℝ, 0 < d → RectangleInversionAt d

def RectangleWedgeStatement : Prop :=
  ∀ d : ℝ, 0 < d → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
    ∀ p ∈ inverseRectangle d, tiltedMap d s p ∈ wedge ↔ p ∈ wedge

end
end SlopeRational

end OAI
