import OAI.Geometry.CylinderCovering.Singular.StreamDefinitions

namespace OAI

noncomputable section

namespace CylinderCovering.SingularStream
open RuledApproximation

def potentialGradient (p : ℝ) (z : Plane) : Plane :=
  vec2 (deriv (fun b : ℝ => potential p b (z 1)) (z 0))
    (deriv (fun r : ℝ => potential p (z 0) r) (z 1))

def potentialHessian (p : ℝ) (z : Plane) : Plane →L[ℝ] Plane :=
  fderiv ℝ (potentialGradient p) z

end CylinderCovering.SingularStream

end

end OAI
