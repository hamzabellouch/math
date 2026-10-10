import OAI.Geometry.Relativity.CKS.LogPhysicalFoliation
import OAI.Geometry.Relativity.CKS.CollarLogSlices

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logTError_three_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hK : ContDiffAt ℝ 3 f.mK x) (hk : ContDiffAt ℝ 3 f.ek x)
    (hp : (logMetric f x).PosDef) : ContDiffAt ℝ 3 (fun y => logT f y-1) x := by
  have he : ContDiffAt ℝ 3 (fun y : Point => Real.exp (y 0)) x := by fun_prop
  have he1 : ContDiffAt ℝ 3 (fun y : Point => 1/Real.exp (y 0)) x :=
    contDiffAt_const.div he (Real.exp_ne_zero _)
  have hq : ContDiffAt ℝ 3 (logGamma f) x :=
    ((he.pow 2).smul hf.sigma |>.add (he1.smul hf.mg)).add hf.eg
  have ht : ContDiffAt ℝ 3 (logTangentialK f) x :=
    ((he.pow 2).smul hf.sigma |>.add (he1.smul hK)).add hk
  have hd : determinant (logGamma f x) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_diff_at hq hd
  unfold logT traceProduct
  apply ContDiffAt.sub _ contDiffAt_const
  apply ContDiffAt.mul contDiffAt_const
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hi i k).mul (component_diff ht k i)

end
end CKSMixedGeometry

end

end OAI
