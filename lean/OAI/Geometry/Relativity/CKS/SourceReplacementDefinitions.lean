import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CutArea
import OAI.Geometry.Relativity.CKS.IntrinsicReplacementDefinitions

namespace OAI

noncomputable section
namespace CKSSourceExterior
noncomputable section
open Set Manifold Bundle MeasureTheory CKSGeometricCuts CKSMetricGluing
open scoped ContDiff
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 CKSGeometricCuts.halfSpaceDimension_neZero) I3 ∞ N _ _]
  [SecondCountableTopology N]

lemma minimumEnclosingArea_eq_toReal (g : SmoothMetric I3 (M := N)) :
    minimumEnclosingArea g = (CKSFullCutArea.minEnclosingArea g).toReal := by
  exact (ENNReal.toReal_iInf (fun D => ne_of_lt (CKSFullCutArea.area_finite g D))).symm

end
end CKSSourceExterior

end

end OAI
