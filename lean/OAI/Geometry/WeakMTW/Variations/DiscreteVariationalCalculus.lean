import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational

 theorem scalar_second_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hn' : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hM := isLocalMax_of_deriv_deriv_neg hn' hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm,hM] with y hy hy'
    exact le_antisymm hy' hy
  have hde : deriv f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [he.deriv] with y hy
    simpa using hy
  have hh := hde.deriv_eq
  simp only [deriv_const] at hh
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hessian_apply {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (h k : E) :
    fderiv ℝ (fun z => fderiv ℝ f z k) x h = fderiv ℝ (fderiv ℝ f) x h k := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  rw [fderiv_clm_apply hd (differentiableAt_const k)]
  simp

 theorem line_second {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  have he : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 0]
      (fun t => fderiv ℝ f (x + t • v) v) := by
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using (hline 0).continuousAt.tendsto
    filter_upwards [ht (hf.eventually (by norm_num))] with t ht'
    change ContDiffAt ℝ 2 f (x+t • v) at ht'
    exact ((ht'.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [he.deriv_eq]
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have haa := hd.clm_apply (hasFDerivAt_const v x)
  have haa' : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((fderiv ℝ f x).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) x).flip v) (x+(0 : ℝ) • v) := by
    simpa using haa
  have hh := haa'.comp_hasDerivAt (0 : ℝ) (hline 0)
  simpa [Function.comp_def] using hh.deriv

 theorem hessian_nonneg {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hm : IsLocalMin f x) (v : E) : 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  rw [← line_second hf v]
  have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hm' : IsLocalMin (fun t : ℝ => f (x + t • v)) 0 := by
    have hm' : IsLocalMin f (x+(0 : ℝ) • v) := by simpa using hm
    exact IsLocalMin.comp_continuous (g := fun t : ℝ => x+t • v) hm' hc
  exact scalar_second_nonneg hm' (hf.continuousAt.comp_of_eq hc (by simp))

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
