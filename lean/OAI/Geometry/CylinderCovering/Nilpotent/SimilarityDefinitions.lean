import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.Nilpotent
open RuledApproximation

def centerMap (z : Space) : Space :=
  vec3 (z 0 / 2) (z 1 / 2) (1 / (2 * Real.sqrt 2) - z 2 / 2)

def uncenterMap (z : Space) : Space :=
  vec3 (2 * z 0) (2 * z 1) (1 / Real.sqrt 2 - 2 * z 2)

end CylinderCovering.Nilpotent

end

end OAI
