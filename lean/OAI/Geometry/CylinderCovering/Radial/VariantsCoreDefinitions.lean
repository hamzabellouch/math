import OAI.Geometry.CylinderCovering.Radial.PairedActualDefinitions
import OAI.Geometry.CylinderCovering.Radial.CapVariantsDefinitions
import OAI.Geometry.CylinderCovering.Radial.SqrtRealizationDefinitions
import OAI.Geometry.CylinderCovering.Footprints.CertificatesDefinitions
import OAI.Geometry.CylinderCovering.Footprints.ConvergenceDefinitions
import OAI.Geometry.CylinderCovering.Physical.PhysicalFootprintsDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.CoreDefinitions
import OAI.Geometry.CylinderCovering.Physical.CoordinateStatementDefinitions
import OAI.Geometry.CylinderCovering.Radial.OverlapDefinitions
import OAI.Geometry.CylinderCovering.Caps.CapsDefinitions
import OAI.Geometry.CylinderCovering.Radial.InducedFieldDefinitions

namespace OAI

namespace CylinderCovering
structure RadialVariantsCoreStatement : Prop where
  paired : RadialPairedSweep.PairedStatement
  actualPaired : RadialPairedSweep.ActualPairedStatement
  linearCubicFractional : RadialCapVariants.LCFStatement
  squareRoot : RadialSqrtCap.FullStatement
  overlapIdentities : RadialOverlap.IdentitiesStatement
  overlapBound : RadialOverlap.ComplementaryBoundStatement
  halfheightCoverage : HalfHeightCaps.CoverageStatement
  halfheightCompensation : HalfHeightCaps.CompensationStatement
  halfheightPhysicalCoverage : HalfHeightCaps.PhysicalCoverageStatement
  footprintCertificates : Footprints.LocalFootprintCertificates
  footprintShapes : Footprints.ShapeStatement
  footprintLimits : RadialFootprints.FootprintConvergenceStatement
  physicalFootprints : PhysicalFootprints.PhysicalStatement
  physicalCoordinates : RadialPhysical.PhysicalCoordinatesStatement
  barycentricCore : BarycentricCoreStatement
  inducedField : RadialInducedField.Statement
end CylinderCovering

end OAI
