import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoff

namespace OAI

/-! Quantitative bounds for the fixed cusp cutoff. Its radial derivative
is supported on the compact annulus with heights between one and two. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_norm (v : ℝ) : ‖cubicThetaCuspCutoff v‖≤1 := by
  rw [cubicThetaCuspCutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma cubicThetaCuspCutoff_deriv_bound :
    ∃ B≥0, ∀ v : ℝ, v^2*‖deriv cubicThetaCuspCutoff v‖^2≤
      (Icc (1:ℝ) 2).indicator (fun _ => B) v := by
  classical
  have hcont : Continuous (fun v : ℝ => v^2*‖deriv cubicThetaCuspCutoff v‖^2) :=
    (continuous_id.pow 2).mul ((cubicThetaCuspCutoff_smooth.continuous_deriv (by simp)).norm.pow 2)
  have hc : HasCompactSupport (fun v : ℝ => v^2*‖deriv cubicThetaCuspCutoff v‖^2) :=
    (cubicThetaCuspCutoff_deriv_compact.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)).mul_left
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
  refine ⟨max C 0,le_max_right _ _,fun v => ?_⟩
  by_cases hv : v∈Icc (1:ℝ) 2
  · rw [indicator_of_mem hv]
    exact (le_abs_self _).trans ((hC v).trans (le_max_left _ _))
  · have hv' : v<1 ∨ 2<v := by simpa only [mem_Icc,not_and_or,not_le] using hv
    rw [indicator_of_notMem hv,(cubicThetaCuspCutoff_derivatives_zero hv').1,
      norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]

lemma cubicThetaComplex_norm_add_young (a b : ℂ) {ε : ℝ} (hε : 0<ε) :
    ‖a+b‖^2≤(1+ε)*‖b‖^2+(1+ε⁻¹)*‖a‖^2 := by
  have ht := norm_add_le a b
  have hs := mul_self_le_mul_self (_root_.norm_nonneg (a+b)) ht
  have hy := two_mul_le_add_mul_sq (a:=‖b‖) (b:=‖a‖) hε
  nlinarith

end CubicFirstMoment

end

end OAI
