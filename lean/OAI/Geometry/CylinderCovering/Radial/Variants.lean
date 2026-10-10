import OAI.Geometry.CylinderCovering.Radial.VariantsDefinitions
import OAI.Geometry.CylinderCovering.Radial.VariantsCore
import OAI.Geometry.CylinderCovering.Footprints.PhysicalConvergence
import OAI.Geometry.CylinderCovering.Physical.Finite
import OAI.Geometry.CylinderCovering.Barycentric.Finite
import OAI.Geometry.CylinderCovering.Caps.FiniteTheorem
import OAI.Geometry.CylinderCovering.Caps.FiniteShape
import OAI.Geometry.CylinderCovering.Caps.Geometry
import OAI.Geometry.CylinderCovering.Physical.Coverage
import OAI.Geometry.CylinderCovering.Footprints.QuadraticPhysicalFootprints
import OAI.Geometry.CylinderCovering.Footprints.Polygon

namespace OAI

namespace CylinderCovering

theorem radialVariants_proof : RadialVariantsStatement where
  core := radialVariantsCore
  physicalFootprintLimits := RadialFootprints.physical_footprint_area_limits
  physicalFinite := RadialPhysical.physical_finite
  barycentricFinite := RadialCoordinates.BarycentricFinite.finite_barycentric_sweeps
  halfheightFinite := HalfheightFinite.full_halfheight
  unitEdge := UnitEdgeFootprints.full_unit_edge

end CylinderCovering

end OAI
