import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_translate_at_zero {f:E → F} {x:E} (hf:DifferentiableAt ℝ f x) (c:F) :
    fderiv ℝ (fun h=>f (x+h)-c) 0=fderiv ℝ f x := by
  rw [fderiv_sub_const]
  have H:=(show HasFDerivAt f (fderiv ℝ f x) (x+id 0) from by simpa only [id_eq,add_zero] using hf.hasFDerivAt).comp 0 ((hasFDerivAt_id (0:E)).const_add x)
  simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using H.fderiv

lemma second_fderiv_translate_at_zero {f:E → F} {x:E} (hf:ContDiffAt ℝ 2 f x) (c:F) :
    fderiv ℝ (fderiv ℝ (fun h=>f (x+h)-c)) 0=fderiv ℝ (fderiv ℝ f) x := by
  have ht:Tendsto (fun h:E=>x+h) (𝓝 0) (𝓝 x):=by
    have hc : ContinuousAt (fun h:E=>x+h) 0 := continuousAt_const.add continuousAt_id
    have H:=hc.tendsto
    rw [add_zero] at H
    exact H
  have hd:∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y:=
    (hf.eventually (by norm_num)).mono (fun _ h=>h.differentiableAt (by norm_num))
  have he:fderiv ℝ (fun h=>f (x+h)-c)=ᶠ[𝓝 (0:E)] (fun h=>fderiv ℝ f (x+h)):=by
    filter_upwards [ht.eventually hd] with h hh
    rw [fderiv_sub_const]
    have H:=hh.hasFDerivAt.comp h ((hasFDerivAt_id h).const_add x)
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using H.fderiv
  rw [he.fderiv_eq]
  have hfd:DifferentiableAt ℝ (fderiv ℝ f) x:=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have H:=(show HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x+id 0) from by simpa only [id_eq,add_zero] using hfd.hasFDerivAt).comp 0 ((hasFDerivAt_id (0:E)).const_add x)
  simpa only [Function.comp_def,add_zero,ContinuousLinearMap.comp_id] using H.fderiv
end WeakMTWTransport

end

end OAI
