import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletInverse
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-! Holomorphy and termwise differentiation of the complete ideal series
on its half-plane of absolute convergence. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

lemma idealDirichlet_term_differentiable (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) :
    Differentiable ℂ (fun s : ℂ => χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
  let : NeZero (idealExponentNorm ν:ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'⟩
  exact (differentiable_const (χ ν)).mul
    ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg)

lemma idealDirichlet_uniform_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (ν : EisensteinIdealExponent)
    {s : ℂ} (hs : σ < s.re) :
    ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ ≤ idealExponentNorm ν^(-σ) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)).trans
  exact Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) (by linarith)

lemma idealDirichlet_differentiableOn_halfPlane (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (normDirichletSeries χ idealExponentNorm) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (summable_ideal_norm_rpow hσ)
  · intro ν
    exact (idealDirichlet_term_differentiable χ ν).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro ν s hs
    exact idealDirichlet_uniform_bound χ hχ ν hs

lemma idealDirichlet_differentiableAt (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (normDirichletSeries χ idealExponentNorm) s := by
  have hσ : 1 < (1+s.re)/2 := by linarith
  have hm : (1+s.re)/2 < s.re := by linarith
  exact (idealDirichlet_differentiableOn_halfPlane χ hχ hσ).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hm)

lemma idealDirichlet_term_hasDerivAt (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) (s : ℂ) :
    HasDerivAt (fun z : ℂ => χ ν*(idealExponentNorm ν:ℂ)^(-z))
      (χ ν*(-(Real.log (idealExponentNorm ν):ℂ))*(idealExponentNorm ν:ℂ)^(-s)) s := by
  have hn : (idealExponentNorm ν:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
  have h := (((hasDerivAt_id s).neg).const_cpow (Or.inl hn)).const_mul (χ ν)
  rw [←Complex.ofReal_log (idealExponentNorm_pos ν).le] at h
  convert h using 1
  · rfl
  · simp only [Pi.neg_apply,id_eq]
    ring

lemma idealDirichlet_hasSum_deriv (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun ν => χ ν*(-(Real.log (idealExponentNorm ν):ℂ))*
      (idealExponentNorm ν:ℂ)^(-s)) (deriv (normDirichletSeries χ idealExponentNorm) s) := by
  have hσ : 1 < (1+s.re)/2 := by linarith
  have hm : (1+s.re)/2 < s.re := by linarith
  have h := Complex.hasSum_deriv_of_summable_norm (summable_ideal_norm_rpow hσ)
    (fun ν => (idealDirichlet_term_differentiable χ ν).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun ν z hz => idealDirichlet_uniform_bound χ hχ ν hz) hm
  simpa only [normDirichletSeries,(idealDirichlet_term_hasDerivAt χ _ _).deriv] using! h

end CubicFirstMoment

end

end OAI
