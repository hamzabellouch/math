import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCapsDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SquaredCapCoverDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.CoverDefinitions
import OAI.Geometry.CylinderCovering.Angular.TableCoverDefinitions

namespace OAI

namespace CylinderCovering.AngularExtensions

def CoreStatement : Prop :=
  AngularGeneral.Statement ∧
  AngularOrdinaryCaps.OrdinaryCoverStatement ∧
  AngularCaps.SquaredCoverStatement ∧
  CartesianCoverStatement

def Statement : Prop := CoreStatement ∧ AngularTableCover.Statement

end CylinderCovering.AngularExtensions

end OAI
