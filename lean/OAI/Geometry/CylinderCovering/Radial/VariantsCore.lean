import OAI.Geometry.CylinderCovering.Radial.VariantsCoreDefinitions
import OAI.Geometry.CylinderCovering.Radial.CapVariants
import OAI.Geometry.CylinderCovering.Radial.SqrtRealization
import OAI.Geometry.CylinderCovering.Radial.PairedActual
import OAI.Geometry.CylinderCovering.Footprints.Certificates
import OAI.Geometry.CylinderCovering.Footprints.Convergence
import OAI.Geometry.CylinderCovering.Physical.PhysicalFootprints
import OAI.Geometry.CylinderCovering.Physical.Coordinates
import OAI.Geometry.CylinderCovering.Barycentric.Core
import OAI.Geometry.CylinderCovering.Radial.Overlap
import OAI.Geometry.CylinderCovering.Caps.Caps
import OAI.Geometry.CylinderCovering.Radial.InducedField

namespace OAI

namespace CylinderCovering

theorem radialVariantsCore : RadialVariantsCoreStatement where
  paired := RadialPairedSweep.paired_radial_sweeps
  actualPaired := RadialPairedSweep.paired_actual_sweeps
  linearCubicFractional := RadialCapVariants.radial_cap_variants
  squareRoot := RadialSqrtCap.full_square_root_cap
  overlapIdentities := RadialOverlap.overlap_identities
  overlapBound := RadialOverlap.complementary_bound
  halfheightCoverage := HalfHeightCaps.halfheight_coverage
  halfheightCompensation := HalfHeightCaps.compensation
  halfheightPhysicalCoverage := HalfHeightCaps.halfheight_physical_coverage
  footprintCertificates := Footprints.localFootprintCertificates
  footprintShapes := Footprints.footprint_shapes
  footprintLimits := RadialFootprints.footprint_area_limits
  physicalFootprints := PhysicalFootprints.physical_footprints
  physicalCoordinates := RadialPhysical.physicalCoordinates_result
  barycentricCore := RadialCoordinates.barycentricCore
  inducedField := RadialInducedField.radial_induced_field

end CylinderCovering

end OAI
