import OAI.Geometry.CylinderCovering.Caps.CapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.HalfHeightCaps.FractionalEstimates

def P (x : ℝ) : ℝ := 1 / 4 + x ^ 2

def g (x : ℝ) : ℝ := x ^ 2 * P x

end CylinderCovering.HalfHeightCaps.FractionalEstimates

end

end OAI
