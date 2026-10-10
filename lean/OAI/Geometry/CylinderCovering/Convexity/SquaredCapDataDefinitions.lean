import OAI.Geometry.CylinderCovering.Angular.CapsDefinitions
import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions

namespace OAI

noncomputable section

namespace AngularCaps

def withSquaredCaps (τ η : ℝ) (D : CylinderCovering.AngularGeneral.Data) :
    CylinderCovering.AngularGeneral.Data :=
  { D with radius := fun _ => squaredRadius τ η }

end AngularCaps

end

end OAI
