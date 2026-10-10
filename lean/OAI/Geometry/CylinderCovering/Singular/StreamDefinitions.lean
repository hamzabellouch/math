import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section

namespace CylinderCovering.SingularStream

def potential (p b r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (r / (1 / 2 : ℝ)) ^ (p - 2) * (b ^ 2 - r ^ 2)

end CylinderCovering.SingularStream

end

end OAI
