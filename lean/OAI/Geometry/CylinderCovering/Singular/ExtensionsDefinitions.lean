import OAI.Geometry.CylinderCovering.Singular.ParameterRangeDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneNormalizationDefinitions
import OAI.Geometry.CylinderCovering.Singular.BasicDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneCoverDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneResultsDefinitions

namespace OAI

namespace CylinderCovering

def SingularExtensionsStatement : Prop :=
  FlexibleSingular.OrthogonalStatement ∧
  SingularEdgeOneCover.FlexibleStatement ∧
  SingularEdgeOneCover.ExactStatement ∧
  SingularEdgeOneCover.AlternativeStatement ∧
  SingularEdgeOneCover.CostStatement ∧
  SingularEdgeOneCover.AlternativeCostStatement ∧
  SingularEdgeOne.DictionaryStatement ∧
  SingularEdgeOneCover.NormalizationStatement ∧
  SingularParameterRange.Statement

end CylinderCovering

end OAI
