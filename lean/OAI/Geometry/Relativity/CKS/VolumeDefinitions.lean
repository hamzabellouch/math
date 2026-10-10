import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.ConstraintDensityDefinitions

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] model_finiteDimensional

attribute [local instance] model_borelSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable [MeasurableSpace M] [BorelSpace M]

end CKSIntrinsicVolume

end

end OAI
