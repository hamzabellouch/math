import OAI.Geometry.CylinderCovering.Singular.ParameterRange
import OAI.Geometry.CylinderCovering.Singular.EdgeOneNormalization
import OAI.Geometry.CylinderCovering.Singular.ExtensionsDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneCost
import OAI.Geometry.CylinderCovering.Singular.EdgeOneResults

namespace OAI

namespace CylinderCovering

theorem singularExtensions_proof : SingularExtensionsStatement :=
  ⟨FlexibleSingular.orthogonal_statement,
    SingularEdgeOneCover.flexible_cover,
    SingularEdgeOneCover.exact_cover,
    SingularEdgeOneCover.alternative_cover,
    SingularEdgeOneCover.cost_statement,
    SingularEdgeOneCover.alternative_cost,
    SingularEdgeOne.dictionary,
    SingularEdgeOneCover.normalization,
    SingularParameterRange.statement⟩

end CylinderCovering

end OAI
