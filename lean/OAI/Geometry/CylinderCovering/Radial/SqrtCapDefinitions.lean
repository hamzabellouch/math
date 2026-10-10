import OAI.Geometry.CylinderCovering.Radial.CapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSqrtCap
open MeasureTheory

abbrev profile := RadialCaps.H

abbrev speedSq := RadialCaps.D0

abbrev cap := RadialCaps.sqrtCap

def cost (β ε : ℝ) : ℝ := RadialCaps.Q (cap β ε) ε

end CylinderCovering.RadialSqrtCap

end

end OAI
