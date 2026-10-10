import OAI.Geometry.CylinderCovering.Nilpotent.FieldDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Nilpotent.Profile
open RuledApproximation

def field (v w : ℝ → ℝ) (b : Plane) : Plane :=
  vec2 (v (b 0 / b 1)) (w (b 0 / b 1))

def derivative (dv dw p t : ℝ) : Plane →L[ℝ] Plane :=
  (t⁻¹ • (EuclideanSpace.proj 0 - p • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ)).smulRight
    (vec2 dv dw)

def TangentAt (v w : ℝ → ℝ) (p : ℝ) : Prop :=
  ∃ μ : ℝ, vec2 (v p) (w p) = μ • vec2 p 1

end CylinderCovering.Nilpotent.Profile

end

end OAI
