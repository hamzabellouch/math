import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter
open scoped Topology ContDiff
namespace SecondCurveChain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem second {f : E → ℝ} {c : ℝ → E} {t : ℝ} {v acc : E}
    (hf : ContDiffAt ℝ 2 f (c t)) (hc : ContDiffAt ℝ 2 c t)
    (hv : HasDerivAt c v t) (ha : HasDerivAt (deriv c) acc t) :
    deriv (deriv (f ∘ c)) t =
      fderiv ℝ (fderiv ℝ f) (c t) v v + fderiv ℝ f (c t) acc := by
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDc := hD.hasFDerivAt.comp_hasDerivAt t hv
  have hprod := hDc.clm_apply ha
  have heq : deriv (f ∘ c) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (c s) (deriv c s)) := by
    have hevent := (hf.eventually (by norm_num)).filter_mono hv.continuousAt.tendsto
    filter_upwards [hevent, hc.eventually (by norm_num)] with s hs hcs
    change ContDiffAt ℝ 2 f (c s) at hs
    exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      (hcs.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [heq.deriv_eq]
  simpa only [Function.comp_def,hv.deriv] using hprod.deriv

end SecondCurveChain
end

end WeakMTWGlobalSupport

end OAI
