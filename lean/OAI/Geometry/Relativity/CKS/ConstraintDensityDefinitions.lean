import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.TailEnergy

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
attribute [local instance] halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric
  CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

end CKSIntrinsicConstraints

end

end OAI
