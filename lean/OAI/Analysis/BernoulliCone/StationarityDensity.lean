import OAI.Analysis.BernoulliCone.HalfspaceDensity

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def stressTerm (u φ : E → ℝ) (e : E) (x : E) : ℝ :=
  density u x * fderiv ℝ φ x e -
    2 * (fderiv ℝ u x e) * (fderiv ℝ u x (gradient φ x))

lemma pullback_gradient {u φ : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hφ : DifferentiableAt ℝ φ x)
    (e : E) (t : ℝ) (h : 1+t*fderiv ℝ φ x e ≠ 0)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) :
    gradient (fun y => u (g.symm y)) (g x) =
      gradient u x - (t*(fderiv ℝ u x e)/(1+t*fderiv ℝ φ x e)) • gradient φ x := by
  have hi := inverse_hasFDerivAt_deform hφ.hasFDerivAt e t h g hg
  have ho : HasFDerivAt u (fderiv ℝ u x) (g.symm (g x)) := by
    simpa using hu.hasFDerivAt
  have hf := ho.comp (g x) hi
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left]
  change fderiv ℝ (u ∘ g.symm) (g x) y = _
  rw [hf.fderiv,dual_rankOneInverse]
  simp only [sub_apply,smul_apply,smul_eq_mul,inner_sub_left,
    real_inner_smul_left,inner_gradient_left]

omit [CompleteSpace E] in
lemma general_density_algebra (q e z : E) (t c : ℝ) (h : 1+t*inner ℝ z e ≠ 0) :
    (1+t*inner ℝ z e) * (‖q-(t*inner ℝ q e/(1+t*inner ℝ z e)) • z‖^2+c) -
      (‖q‖^2+c) =
      t*((‖q‖^2+c)*inner ℝ z e - 2*inner ℝ q e*inner ℝ q z) +
        t^2*(inner ℝ q e)^2*‖z‖^2/(1+t*inner ℝ z e) := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  field_simp
  ring

lemma stress_density_bound {u φ : E → ℝ} {L C : ℝ≥0} {x : E}
    (hu : DifferentiableAt ℝ u x) (huLip : LipschitzWith L u)
    (hφ : DifferentiableAt ℝ φ x) (hφLip : LipschitzWith C φ)
    (e : E) (t : ℝ) (h : (1:ℝ)/2 ≤ 1+t*fderiv ℝ φ x e)
    (g : E ≃ₜ E) (hg : ∀ y, g y=deform φ e t y) :
    (1+t*fderiv ℝ φ x e)*density (fun y => u (g.symm y)) (g x) ≤
      density u x+t*stressTerm u φ e x+t^2*(2*(L:ℝ)^2*‖e‖^2*(C:ℝ)^2) := by
  have hp : 0 < 1+t*fderiv ℝ φ x e := lt_of_lt_of_le (by norm_num) h
  have hne := hp.ne'
  have hq := gradient_norm_le_lipschitz huLip hu
  have hz := gradient_norm_le_lipschitz hφLip hφ
  have hq2 : ‖gradient u x‖^2 ≤ (L:ℝ)^2 := by nlinarith [norm_nonneg (gradient u x)]
  have hz2 : ‖gradient φ x‖^2 ≤ (C:ℝ)^2 := by nlinarith [norm_nonneg (gradient φ x)]
  have hqe : (fderiv ℝ u x e)^2 ≤ (L:ℝ)^2*‖e‖^2 := by
    have hh := real_inner_mul_inner_self_le (gradient u x) e
    rw [inner_gradient_left,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,← pow_two] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hq2 (sq_nonneg _))
  have hnum : 0 ≤ t^2*((L:ℝ)^2*‖e‖^2*(C:ℝ)^2) := by positivity
  have hbound : t^2*(fderiv ℝ u x e)^2*‖gradient φ x‖^2 ≤
      t^2*((L:ℝ)^2*‖e‖^2*(C:ℝ)^2) := by
    have hh := mul_le_mul hqe hz2 (sq_nonneg _) (by positivity : 0 ≤ (L:ℝ)^2*‖e‖^2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg t)
  have hr : t^2*(fderiv ℝ u x e)^2*‖gradient φ x‖^2/(1+t*fderiv ℝ φ x e) ≤
      t^2*(2*(L:ℝ)^2*‖e‖^2*(C:ℝ)^2) := by
    apply (div_le_iff₀ hp).mpr
    have hh : t^2*((L:ℝ)^2*‖e‖^2*(C:ℝ)^2) ≤
        (2*(t^2*((L:ℝ)^2*‖e‖^2*(C:ℝ)^2)))*(1+t*fderiv ℝ φ x e) := by nlinarith
    exact hbound.trans (by nlinarith only [hh])
  have hc := general_density_algebra (gradient u x) e (gradient φ x) t
    (if 0 < u x then 1 else 0) (by simpa only [inner_gradient_left] using hne)
  simp only [inner_gradient_left] at hc
  rw [density,pullback_gradient hu hφ e t hne g hg,g.symm_apply_apply]
  unfold stressTerm density
  linarith
end Bernoulli.Shape

end
end

end OAI
