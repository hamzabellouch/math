import OAI.Geometry.CylinderCovering.Nilpotent.BasicDefinitions
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section

namespace CylinderCovering.Nilpotent

open RuledApproximation

def signedField (σ k : ℝ) (b : Plane) : Plane :=
  vec2 (σ * k * v (b 0 / b 1)) (σ * k * w (b 0 / b 1))

def angularDerivative (σ k : ℝ) (b : Plane) : Plane →L[ℝ] Plane :=
  (σ * k / (2 * b 1)) •
    (EuclideanSpace.proj 0 - (b 0 / b 1) • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight
      (vec2 (b 0 / b 1) 1)

end CylinderCovering.Nilpotent

end

end OAI
