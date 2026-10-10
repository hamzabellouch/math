import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CutSurface

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]
  [SecondCountableTopology N]

end CKSFullCutArea

end

end OAI
