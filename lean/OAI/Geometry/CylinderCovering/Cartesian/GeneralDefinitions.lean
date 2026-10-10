import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.CapsDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.CartesianCaps

def withCartesianCaps (τ η : ℝ) (D : AngularGeneral.Data) : AngularGeneral.Data :=
  { D with radius := fun _ => cap τ η }

end CylinderCovering.CartesianCaps

end

end OAI
