import OAI.Analysis.FiniteFactor.OperatorTracialRepresentation
import OAI.Analysis.FiniteFactor.CrossedProduct.FiniteAlgebra

namespace OAI

namespace FiniteFactor
noncomputable section

/-- Actual instantiation of the certified tracial-representation API.
Both central obligations are proved for this source algebra. -/
def sourceTracialRepresentation (θ : SourceCoordinate → ℝ) :
    TracialRepresentation (sourceAlgebra θ) where
  vector := sourceVacuum
  norm_vector := sourceVacuum_norm
  cyclic := fun S T => sourceVacuumFunctional_tracial θ S.property T.property
  separating := fun T hT => Subtype.ext (sourceVacuum_separating θ T.property hT)

theorem sourceTracialRepresentation_trace (θ : SourceCoordinate → ℝ)
    (T : (sourceAlgebra θ).toStarSubalgebra) :
    (sourceTracialRepresentation θ).trace T = sourceVacuumFunctional T := rfl

theorem sourceTracialRepresentation_normal (θ : SourceCoordinate → ℝ) :
    @Continuous _ _ (sourceAlgebraUltraweakTopology θ) inferInstance
      (sourceTracialRepresentation θ).trace :=
  sourceVacuumFunctional_algebra_normal θ

end
end FiniteFactor

end OAI
