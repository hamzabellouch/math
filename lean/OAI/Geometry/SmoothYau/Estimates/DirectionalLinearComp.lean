import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma directional_linear_comp (L : E →L[ℝ] F) {f : F → ℂ}
    (hf : Differentiable ℝ f) (x v : E) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf _) L.differentiableAt,L.fderiv]
  rfl
lemma second_linear_comp (L : E →L[ℝ] F) {f : F → ℂ}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ L) y w) x v =
      fderiv ℝ (fun y => fderiv ℝ f y (L w)) (L x) (L v) := by
  simp_rw [directional_linear_comp L (hf.differentiable (by simp))]
  exact directional_linear_comp L
    (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x v
lemma directional_mul_complex {f g : E → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x v : E) :
    fderiv ℝ (fun y => f y*g y) x v = fderiv ℝ f x v*g x+f x*fderiv ℝ g x v := by
  have hh := ((hf x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv
  change fderiv ℝ (f*g) x v = _
  rw [hh]
  simp [smul_eq_mul,mul_comm,add_comm]
lemma second_mul_complex {f g : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f z*g z) y w) x v =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v*g x +
      fderiv ℝ f x w*fderiv ℝ g x v +
      fderiv ℝ f x v*fderiv ℝ g x w +
      f x*fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hd := hf.differentiable (by simp)
  have he := hg.differentiable (by simp)
  have hd' := ((hf.fderiv_right (m:=∞) (by simp)).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun (_:E) => w))).differentiable (by simp)
  have he' := ((hg.fderiv_right (m:=∞) (by simp)).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun (_:E) => w))).differentiable (by simp)
  simp_rw [directional_mul_complex hd he]
  change fderiv ℝ ((fun y => fderiv ℝ f y w)*g+f*(fun y => fderiv ℝ g y w)) x v = _
  rw [fderiv_add ((hd' x).mul (he x)) ((hd x).mul (he' x))]
  simp only [add_apply]
  change fderiv ℝ (fun y => fderiv ℝ f y w*g y) x v + fderiv ℝ (fun y => f y*fderiv ℝ g y w) x v = _
  rw [directional_mul_complex hd' he,directional_mul_complex hd he']
  ring
end YauCounterexamples
end

end OAI
