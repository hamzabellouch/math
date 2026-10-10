import Mathlib

namespace OAI

/-! The third-order integral remainder needed after the finite quadratic
mean correction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma quadraticTaylor_value {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    taylorWithinEval f 2 (uIcc (0 : ℝ) 1) 0 1 =
      f 0 + deriv f 0 + (1 / 2 : ℝ) • iteratedDeriv 2 f 0 := by
  have hi (k : ℕ) : iteratedDerivWithin k f (uIcc (0 : ℝ) 1) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      ((hf.of_le (by simp : (k : ℕ∞ω) ≤ ∞)).contDiffAt) (by simp)
  rw [show 2 = 1 + 1 from rfl, taylorWithinEval_succ, taylorWithinEval_succ,
    taylor_within_zero_eval, hi 1, hi 2]
  norm_num

lemma cubicTaylor_remainder {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    f 1 - f 0 - deriv f 0 - (1 / 2 : ℝ) • iteratedDeriv 2 f 0 =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • iteratedDeriv 3 f t := by
  have ht := taylor_integral_remainder (f := f) (n := 2) (x₀ := 0) (x := 1)
    (hf.of_le (by simp : ((2 + 1 : ℕ) : ℕ∞ω) ≤ ∞)).contDiffOn
  rw [quadraticTaylor_value hf] at ht
  have hi : (∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
      iteratedDerivWithin 3 f (uIcc (0 : ℝ) 1) t) =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • iteratedDeriv 3 f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      ((hf.of_le (by simp : (3 : ℕ∞ω) ≤ ∞)).contDiffAt) ht]
    norm_num
  rw [hi] at ht
  convert ht using 1
  abel

lemma cubicTaylor_bound {f : ℝ → E} (hf : ContDiff ℝ ∞ f) {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 3 f t‖ ≤ M) :
    ‖f 1 - f 0 - deriv f 0 - (1 / 2 : ℝ) • iteratedDeriv 2 f 0‖ ≤ M / 2 := by
  rw [cubicTaylor_remainder hf]
  have hbound : ‖∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • iteratedDeriv 3 f t‖ ≤
      (M / 2) * |1 - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa using uIoc_subset_uIcc ht
    have hweight : (1 - t) ^ 2 / 2 ≤ (1 / 2 : ℝ) := by nlinarith [ht'.1, ht'.2]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 - t) ^ 2 / 2)]
    calc
      _ ≤ ((1 - t) ^ 2 / 2) * M := mul_le_mul_of_nonneg_left (hderiv t ht') (by positivity)
      _ ≤ (1 / 2 : ℝ) * M := mul_le_mul_of_nonneg_right hweight hM
      _ = M / 2 := by ring
  simpa using hbound

end ClosedSurfaceR4

end

end OAI
