import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildPosition
import OAI.Geometry.Relativity.CKS.CutSurface

namespace OAI

noncomputable section
open Set Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts CKSSphericalHarmonics
open scoped ContDiff Topology
namespace CKSSourceExterior
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

attribute [local instance] CKSGeometricCuts.halfSpaceDimension_neZero id_invPair
  source_manifold_one

attribute [local instance] source_trivialization_isLinear

end CKSSourceExterior

end

end OAI
