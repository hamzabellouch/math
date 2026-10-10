import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildRoundMetric
import OAI.Geometry.Relativity.CKS.SurfaceScaling
import OAI.Geometry.Relativity.CKS.CutSurface

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface CKSFullCutArea CKSSurfaceVolume
def boundaryScaledMetric {m : ℝ} (hm : 0 < m) :=
  scaledMetric sphereMetric ((2*m)^2) (sq_pos_of_pos (mul_pos (by norm_num) hm))

end CKSSchwarzschild

end

end OAI
