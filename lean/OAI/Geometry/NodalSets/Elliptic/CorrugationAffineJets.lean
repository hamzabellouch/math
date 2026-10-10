import OAI.Geometry.NodalSets.Charts.ChartedEnvelope

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma affine_scalar_first (f : F → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (y x v : E) :
    fderiv ℝ (fun z ↦ f (L (z-y))) x v = fderiv ℝ f (L (x-y)) (L v) := by
  have h := (hf.differentiable (by simp) _).hasFDerivAt.comp x
    (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))
  simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] ℝ ↦ A v) h.fderiv

lemma affine_scalar_second (f : F → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (y x u v : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f (L (z-y)))) x u v =
      fderiv ℝ (fderiv ℝ f) (L (x-y)) (L u) (L v) := by
  have hcomp : ContDiff ℝ ∞ (fun z ↦ f (L (z-y))) :=
    hf.comp (L.contDiff.comp (contDiff_id.sub contDiff_const))
  have hd := (hcomp.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have he := congrArg (fun A : E →L[ℝ] ℝ ↦ A u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he]
  have hfun : (fun z ↦ fderiv ℝ (fun w ↦ f (L (w-y))) z v) =
      (fun z ↦ fderiv ℝ f (L (z-y)) (L v)) :=
    funext (fun z ↦ affine_scalar_first f hf L y z v)
  rw [hfun]
  have hdf := ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (L (x-y))).hasFDerivAt
  have h := (hdf.comp x (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))).clm_apply
    (hasFDerivAt_const (L v) x)
  simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] ℝ ↦ A u) h.fderiv

lemma scalar_product_second (f k : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hk : ContDiff ℝ ∞ k) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f z*k z)) x u v =
      fderiv ℝ (fderiv ℝ f) x u v*k x +
      fderiv ℝ f x v*fderiv ℝ k x u +
      fderiv ℝ f x u*fderiv ℝ k x v +
      f x*fderiv ℝ (fderiv ℝ k) x u v := by
  have hd := (((hf.mul hk).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  have he := congrArg (fun A : E →L[ℝ] ℝ ↦ A u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he]
  have hfun : (fun z ↦ fderiv ℝ (fun w ↦ f w*k w) z v) =
      (fun z ↦ fderiv ℝ f z v*k z+f z*fderiv ℝ k z v) := by
    funext z
    change fderiv ℝ (f*k) z v = _
    rw [fderiv_mul (hf.differentiable (by simp) z) (hk.differentiable (by simp) z)]
    simp
    ring
  rw [hfun]
  have df := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x))
  have dk := (((hk.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x))
  change fderiv ℝ ((fun z ↦ fderiv ℝ f z v)*k+f*(fun z ↦ fderiv ℝ k z v)) x u = _
  rw [((df.mul (hk.differentiable (by simp) x).hasFDerivAt).add
    ((hf.differentiable (by simp) x).hasFDerivAt.mul dk)).fderiv]
  simp
  ring

end
end Yau.Geometry

end OAI
