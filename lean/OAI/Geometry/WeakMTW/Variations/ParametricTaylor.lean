import Mathlib
import OAI.Geometry.WeakMTW.Variations.MovingTaylor

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem param_first_limit {f : E × F → ℝ} {a e : E} {b : F}
    (hf : ContDiffAt ℝ ∞ f (a,b))
    {x d : ℕ → E} {q : ℕ → F} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hq : Tendsto q atTop (𝓝 b))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j,q j)-f (x j,q j))/l j)
      atTop (𝓝 (fderiv ℝ f (a,b) (e,0))) := by
  simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using
    first_limit hf (hx.prodMk_nhds hq) (hd.prodMk_nhds (tendsto_const_nhds (x := (0 : F)))) hl hlne

 theorem param_second_limit {f : E × F → ℝ} {a e : E} {b : F}
    (hf : ContDiffAt ℝ ∞ f (a,b))
    {x d : ℕ → E} {q : ℕ → F} {l : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 a)) (hd : Tendsto d atTop (𝓝 e))
    (hq : Tendsto q atTop (𝓝 b))
    (hl : Tendsto l atTop (𝓝 0)) (hlne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (f (x j+l j•d j,q j)-f (x j,q j)-
        l j*fderiv ℝ f (x j,q j) (d j,0))/(l j)^2)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) (a,b) (e,0) (e,0) / 2)) := by
  have hscale (j : ℕ) : fderiv ℝ f (x j,q j) (l j•d j,0) =
      l j*fderiv ℝ f (x j,q j) (d j,0) := by
    simpa only [Prod.smul_mk,smul_zero,smul_eq_mul] using
      (fderiv ℝ f (x j,q j)).map_smul (l j) (d j,0)
  simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero,hscale] using
    second_limit hf (hx.prodMk_nhds hq) (hd.prodMk_nhds (tendsto_const_nhds (x := (0 : F)))) hl hlne
end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
