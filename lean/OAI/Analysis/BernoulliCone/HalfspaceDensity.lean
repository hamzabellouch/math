import OAI.Analysis.BernoulliCone.HalfspacePullback

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def density (u : E → ℝ) (x : E) : ℝ := ‖gradient u x‖^2+if 0 < u x then 1 else 0

def firstTerm (φ : E → ℝ) (e : E) (x : E) : ℝ :=
  if 0 < inner ℝ e x then fderiv ℝ φ x e else 0

lemma density_nonneg (u : E → ℝ) (x : E) : 0 ≤ density u x := by
  unfold density
  split_ifs <;> positivity

lemma gradient_norm_le_lipschitz {φ : E → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) {x : E} (hd : DifferentiableAt ℝ φ x) :
    ‖gradient φ x‖ ≤ C := by
  rw [gradient,LinearIsometryEquiv.norm_map]
  exact hd.hasFDerivAt.le_of_lipschitz hφ

lemma density_pullback_bound {φ : E → ℝ} {C : ℝ≥0} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hLip : LipschitzWith C φ)
    (e : E) (t : ℝ) (h : (1:ℝ)/2 ≤ 1+t*fderiv ℝ φ x e)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) (hx : inner ℝ e x ≠ 0) :
    (1+t*fderiv ℝ φ x e)*density (fun y => positiveLinear e (g.symm y)) (g x) ≤
      density (positiveLinear e) x + t*(1-‖e‖^2)*firstTerm φ e x +
        t^2*(2*‖e‖^4*C^2) := by
  have hpos : 0 < 1+t*fderiv ℝ φ x e := lt_of_lt_of_le (by norm_num) h
  have hne := hpos.ne'
  have hv : positiveLinear e (g.symm (g x)) = positiveLinear e x := by rw [g.symm_apply_apply]
  rcases lt_or_gt_of_ne hx with hx|hx
  · rw [density,pullback_gradient_neg hφ e t hne g hg hx,hv,density,
      positiveLinear_gradient_neg e hx,firstTerm]
    simp only [positiveLinear,max_eq_right hx.le,lt_self_iff_false,ite_false,norm_zero,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_add,mul_zero,add_zero,not_lt.mpr hx.le]
    positivity
  · have hgNorm := gradient_norm_le_lipschitz hLip hφ
    have hsq : ‖gradient φ x‖^2 ≤ (C:ℝ)^2 := by nlinarith [norm_nonneg (gradient φ x),C.coe_nonneg]
    have hnum : 0 ≤ t^2*‖e‖^4 := mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have hn : 0 ≤ t^2*‖e‖^4*(C:ℝ)^2 := mul_nonneg hnum (sq_nonneg _)
    have hr : t^2*‖e‖^4*‖gradient φ x‖^2/(1+t*fderiv ℝ φ x e) ≤
        t^2*(2*‖e‖^4*C^2) := by
      apply (div_le_iff₀ hpos).mpr
      have h1 := mul_le_mul_of_nonneg_left hsq hnum
      have h2 : t^2*‖e‖^4*(C:ℝ)^2 ≤ (2*(t^2*‖e‖^4*(C:ℝ)^2))*(1+t*fderiv ℝ φ x e) := by
        nlinarith
      apply h1.trans
      calc
        _ ≤ (2*(t^2*‖e‖^4*(C:ℝ)^2))*(1+t*fderiv ℝ φ x e) := h2
        _ = _ := by ring
    have hc := pullback_density_algebra e (gradient φ x) t (by simpa only [inner_gradient_right,conj_trivial] using hne)
    simp only [inner_gradient_right,conj_trivial] at hc
    rw [density,pullback_gradient_pos hφ e t hne g hg hx,hv,density,
      positiveLinear_gradient_pos e hx,firstTerm,ite_eq_left hx]
    simp only [positiveLinear,max_eq_left hx.le,ite_eq_left hx]
    linarith
end Bernoulli.Shape

end
end

end OAI
