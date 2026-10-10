import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section CriticalChain
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_at_critical {f : F → ℝ} {g : E → F} {p : E}
    (hf : ContDiffAt ℝ 2 f (g p)) (hg : ContDiffAt ℝ 2 g p)
    (hzero : fderiv ℝ f (g p)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) p v w=
      fderiv ℝ (fderiv ℝ f) (g p) (fderiv ℝ g p v) (fderiv ℝ g p w) := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hn : ∀ᶠ a in 𝓝 p, DifferentiableAt ℝ g a ∧ DifferentiableAt ℝ f (g a) := by
    have hnG := (hg.of_le (m := 1) (by norm_num)).eventually (by norm_num)
    have hnF := hg.continuousAt.eventually ((hf.of_le (m := 1) (by norm_num)).eventually (by norm_num))
    filter_upwards [hnG,hnF] with a ha hb
    exact ⟨ha.differentiableAt (by norm_num),hb.differentiableAt (by norm_num)⟩
  have heq : fderiv ℝ (f ∘ g) =ᶠ[𝓝 p]
      (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) :=
    hn.mono (fun a ha => fderiv_comp a ha.2 ha.1)
  have hD := (hdf.hasFDerivAt.comp p (hg.differentiableAt (by norm_num)).hasFDerivAt).clm_comp hdg.hasFDerivAt
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) (heq.fderiv_eq.trans hD.fderiv)
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, Function.comp_apply,
    hzero, ContinuousLinearMap.zero_comp,_root_.zero_apply,zero_add] using H

end CriticalChain
end WeakMTWTransport

end

end

end

end OAI
