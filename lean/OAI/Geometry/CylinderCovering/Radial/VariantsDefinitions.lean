import OAI.Geometry.CylinderCovering.Radial.VariantsCoreDefinitions
import OAI.Geometry.CylinderCovering.Footprints.PhysicalConvergenceDefinitions
import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Physical.PairedDefinitions

namespace OAI

namespace CylinderCovering
structure RadialVariantsStatement : Prop where
  core : RadialVariantsCoreStatement
  physicalFootprintLimits : RadialFootprints.PhysicalFootprintConvergenceStatement
  physicalFinite : RadialPhysical.PhysicalFiniteStatement
  barycentricFinite : RadialCoordinates.BarycentricFinite.Statement
  halfheightFinite : HalfheightFinite.Statement
  unitEdge : UnitEdgeFootprints.FullStatement
end CylinderCovering

end OAI
