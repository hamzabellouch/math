import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights

namespace OAI

/-! The radial derivative bounds of a logarithmic family, used to apply
the published prime Siegel–Walfisz input by actual partial summation. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma LogarithmicWeightFamily.norm_log_bound {γ : Type*}
    {L : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily L W) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i x, ‖W i x‖ ≤ C*(1+Real.log (L i))^A := by
  obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound 0
  refine ⟨C,A,hC,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    simpa only [norm_iteratedFDeriv_zero,he] using hbound i (-Real.log x)
  · have hz : W i x = 0 := by
      by_contra hn
      exact hx (h.positive i (subset_closure hn))
    rw [hz,norm_zero]
    exact mul_nonneg hC (pow_nonneg (by linarith [Real.log_nonneg (h.length_one i)]) _)

lemma LogarithmicWeightFamily.radial_deriv_bound {γ : Type*}
    {L : γ → ℝ} {W : γ → ℝ → ℂ} (h : LogarithmicWeightFamily L W) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ i x, 0 < x →
      ‖deriv (W i) x‖*x ≤ C*(1+Real.log (L i))^A := by
  obtain ⟨C,A,hC,hbound⟩ := h.derivative_bound 1
  refine ⟨C,A,hC,?_⟩
  intro i x hx
  let v := -Real.log x
  have hexp : Real.exp (-v) = x := by simp [v,Real.exp_log hx]
  have hdW : HasDerivAt (W i) (deriv (W i) x) x :=
    ((h.smooth i).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdE : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-x) v := by
    have hh := ((hasDerivAt_id v).neg.exp)
    change HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-v)*(-1)) v at hh
    simpa only [hexp,mul_neg,mul_one] using
      hh
  have hd := (show HasDerivAt (W i) (deriv (W i) x) (Real.exp (-v)) by
    rwa [hexp]).scomp v hdE
  have heq : ‖deriv (fun t : ℝ => W i (Real.exp (-t))) v‖ = ‖deriv (W i) x‖*x := by
    change ‖deriv (W i ∘ fun t : ℝ => Real.exp (-t)) v‖ = _
    rw [hd.deriv,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hx,mul_comm]
  have hb := hbound i v
  rw [norm_iteratedFDeriv_one,← norm_deriv_eq_norm_fderiv,heq] at hb
  exact hb

end CubicFirstMoment

end

end OAI
