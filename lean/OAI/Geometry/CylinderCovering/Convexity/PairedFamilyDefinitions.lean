import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
namespace CylinderCovering
open RuledApproximation

def pairedFamily {m : ℕ} (C D : Fin m → Cylinder) : Fin (2 * m) → Cylinder :=
  fun i => Fin.append C D (Fin.cast (two_mul m) i)

end CylinderCovering

end

end OAI
