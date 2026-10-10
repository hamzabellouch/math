import Mathlib
import OAI.Geometry.WeakMTW.Variations.DiscreteVariationalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hessian_split {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (s t C : ℝ) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun z => f z / s + C - g z / t)) x ξ ξ =
      fderiv ℝ (fderiv ℝ f) x ξ ξ / s - fderiv ℝ (fderiv ℝ g) x ξ ξ / t := by
  let F : ℝ → ℝ := fun u => f (x+u•ξ)
  let G : ℝ → ℝ := fun u => g (x+u•ξ)
  have hline : ContDiff ℝ 2 (fun u : ℝ => x+u•ξ) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hF : ContDiffAt ℝ 2 F 0 := by
    have hh : ContDiffAt ℝ 2 f (x+(0 : ℝ)•ξ) := by simpa using hf
    exact hh.comp 0 hline.contDiffAt
  have hG : ContDiffAt ℝ 2 G 0 := by
    have hh : ContDiffAt ℝ 2 g (x+(0 : ℝ)•ξ) := by simpa using hg
    exact hh.comp 0 hline.contDiffAt
  have hcombo := ((hf.div_const s).add (contDiffAt_const (c := C))).sub (hg.div_const t)
  rw [← line_second hcombo ξ,← line_second hf ξ,← line_second hg ξ]
  have hh := iteratedDeriv_sub (n := 2)
    (((contDiffAt_const (c := C)).add (hF.div_const s))) (hG.div_const t)
  rw [iteratedDeriv_const_add (by norm_num),iteratedDeriv_div_const,iteratedDeriv_div_const] at hh
  have heq : ((fun u : ℝ => C + F u / s) - fun u => G u / t) =
      (fun u : ℝ => f (x+u•ξ)/s+C-g (x+u•ξ)/t) := by
    funext u
    simp only [Pi.sub_apply,F,G]
    ring
  rw [heq] at hh
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def,F,G] using hh

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
