import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Convexity.OpenBaseApproximationDefinitions

namespace OAI

noncomputable section
open Set

namespace TriangularCovering

def TriCylinder.toCylinder (C : TriCylinder) : RuledApproximation.Cylinder where
  axis := C.axis
  unit_axis := C.unit_axis
  base := {x | (x : Space) ∈ C.base}

end TriangularCovering

end

end OAI
