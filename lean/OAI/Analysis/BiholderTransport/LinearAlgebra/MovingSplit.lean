import Mathlib

namespace OAI

section

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma pair_hessian_snd_from_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E × E → ℝ} {p : E} (hB : ContDiffAt ℝ 2 B (0,p))
    (u : E × E) {g : E → ℝ} {D : E →L[ℝ] ℝ}
    (heq : (fun v : E => fderiv ℝ B (0,v) u) =ᶠ[𝓝 p] g)
    (hg : HasFDerivAt g D p) (k : E) :
    fderiv ℝ (fderiv ℝ B) (0,p) (0,k) u = D k := by
  have hdf := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hL : HasFDerivAt (fun v : E => ((0:E),v))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) p :=
    (hasFDerivAt_const (0:E) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := ((hdf.hasFDerivAt.comp (f := fun v : E => ((0:E),v)) p hL).clm_apply
    (hasFDerivAt_const u p)).fderiv
  have H := congrArg (fun A : E →L[ℝ] ℝ => A k)
    (hd.symm.trans (heq.fderiv_eq.trans hg.fderiv))
  simpa only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,map_zero,zero_add,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply] using H

end WeakMTWTransport
end
end
end

end OAI
