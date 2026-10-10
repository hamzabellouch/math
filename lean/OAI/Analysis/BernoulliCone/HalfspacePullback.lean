import OAI.Analysis.BernoulliCone.ShapeDiffeomorphism

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def positiveLinear (e : E) (x : E) : ℝ := max (inner ℝ e x) 0

omit [CompleteSpace E] in
lemma positiveLinear_lipschitz (e : E) : LipschitzWith ‖innerSL ℝ e‖₊ (positiveLinear e) :=
  (innerSL ℝ e).lipschitzWith.max_const 0

omit [CompleteSpace E] in
lemma positiveLinear_deriv_pos (e : E) {x : E} (hx : 0 < inner ℝ e x) :
    HasFDerivAt (positiveLinear e) (innerSL ℝ e) x := by
  have he : positiveLinear e =ᶠ[𝓝 x] (innerSL ℝ e) := by
    filter_upwards [(isOpen_lt continuous_const (innerSL ℝ e).continuous).mem_nhds hx] with y hy
    exact max_eq_left hy.le
  exact (innerSL ℝ e).hasFDerivAt.congr_of_eventuallyEq he

omit [CompleteSpace E] in
lemma positiveLinear_deriv_neg (e : E) {x : E} (hx : inner ℝ e x < 0) :
    HasFDerivAt (positiveLinear e) (0 : E →L[ℝ] ℝ) x := by
  have he : positiveLinear e =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [(isOpen_lt (innerSL ℝ e).continuous continuous_const).mem_nhds hx] with y hy
    exact max_eq_right hy.le
  exact (hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) x).congr_of_eventuallyEq he

lemma positiveLinear_gradient_pos (e : E) {x : E} (hx : 0 < inner ℝ e x) :
    gradient (positiveLinear e) x=e := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left,(positiveLinear_deriv_pos e hx).fderiv]
  rfl

lemma positiveLinear_gradient_neg (e : E) {x : E} (hx : inner ℝ e x < 0) :
    gradient (positiveLinear e) x=0 := by
  rw [gradient,(positiveLinear_deriv_neg e hx).fderiv,map_zero]

lemma pullback_gradient_pos {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ x)
    (e : E) (t : ℝ) (h : 1+t*fderiv ℝ φ x e ≠ 0)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) (hx : 0 < inner ℝ e x) :
    gradient (fun y => positiveLinear e (g.symm y)) (g x) =
      e - (t*‖e‖^2/(1+t*fderiv ℝ φ x e)) • gradient φ x := by
  have hi := inverse_hasFDerivAt_deform hφ.hasFDerivAt e t h g hg
  have ho : HasFDerivAt (positiveLinear e) (innerSL ℝ e) (g.symm (g x)) := by
    simpa using positiveLinear_deriv_pos e hx
  have hf := ho.comp (g x) hi
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left]
  change fderiv ℝ (positiveLinear e ∘ g.symm) (g x) y = _
  rw [hf.fderiv,dual_rankOneInverse]
  simp only [sub_apply,smul_apply,smul_eq_mul,
    innerSL_apply_apply,real_inner_self_eq_norm_sq,inner_sub_left,real_inner_smul_left,
    inner_gradient_left]

lemma pullback_gradient_neg {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ x)
    (e : E) (t : ℝ) (h : 1+t*fderiv ℝ φ x e ≠ 0)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) (hx : inner ℝ e x < 0) :
    gradient (fun y => positiveLinear e (g.symm y)) (g x) = 0 := by
  have hi := inverse_hasFDerivAt_deform hφ.hasFDerivAt e t h g hg
  have ho : HasFDerivAt (positiveLinear e) (0 : E →L[ℝ] ℝ) (g.symm (g x)) := by
    simpa using positiveLinear_deriv_neg e hx
  have hf := ho.comp (g x) hi
  change gradient (positiveLinear e ∘ g.symm) (g x) = 0
  rw [gradient,hf.fderiv]
  simp

omit [CompleteSpace E] in
lemma pullback_density_algebra (e z : E) (t : ℝ) (h : 1+t*inner ℝ e z ≠ 0) :
    (1+t*inner ℝ e z) * (‖e-(t*‖e‖^2/(1+t*inner ℝ e z)) • z‖^2+1) -
      (‖e‖^2+1) = t*(1-‖e‖^2)*inner ℝ e z +
        t^2*‖e‖^4*‖z‖^2/(1+t*inner ℝ e z) := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  field_simp
  ring
end Bernoulli.Shape

end
end

end OAI
