import OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbola
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace OAI

/-! Recover an ordinary mean from its logarithmically weighted sum.
The absolute error is at most N for a one-bounded sequence. -/

namespace TwoPointCorrelations

open Finset

lemma halasz_sum_log_factorial (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

lemma halasz_sum_log_gap (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log (n : ℝ))) ≤ N := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, halasz_sum_log_factorial]
  have hst := Stirling.le_log_factorial_stirling (Nat.ne_zero_of_lt hN)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
  simp only [Nat.add_sub_cancel] at *
  linarith

lemma halasz_logarithmic_sum_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Icc 1 N, f n) * (Real.log (N : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ ≤ (N : ℝ) := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have he : S * (Real.log (N : ℝ) : ℂ) - W =
      ∑ n ∈ Icc 1 N, f n * ((Real.log (N : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) := by
    dsimp [S, W]
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum ?_).trans (halasz_sum_log_gap N hN)
  intro n hn
  have hn' := mem_Icc.mp hn
  have hlog : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact mul_le_of_le_one_left hlog (hf n hn'.1)

theorem halasz_logarithmic_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ + N := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have hgap := halasz_logarithmic_sum_error f hf N hN
  have hh := norm_add_le W (S * (Real.log (N : ℝ) : ℂ) - W)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hnorm : ‖S * (Real.log (N : ℝ) : ℂ)‖ = Real.log (N : ℝ) * ‖S‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN, mul_comm]
  rw [add_sub_cancel, hnorm] at hh
  exact hh.trans (add_le_add le_rfl hgap)

end TwoPointCorrelations

end OAI
