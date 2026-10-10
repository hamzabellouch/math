import Mathlib.Analysis.Complex.AbsMax
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteAnalyticZeroFactors

namespace OAI

/-! # Removing finitely many zeros preserves the required logarithmic growth -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem finite_zero_quotient_log_growth (f g : ℂ → ℂ) (S : Finset ℂ) (R : ℕ)
    (hS : ∀ z ∈ S, ‖z‖ ≤ (R : ℝ)) (A : ℝ) (_hA : 0 < A)
    (hg : ∀ z, AnalyticAt ℂ g z) (hne : ∀ z, g z ≠ 0)
    (he : ∀ z, f z = finiteZeroPolynomial f S z * g z)
    (hf : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ (N : ℝ) + 1 →
      Real.log ‖f z‖ ≤ A * ((N : ℝ) + 3) * (1 + Real.log ((N : ℝ) + 3))) :
    ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ (N : ℝ) + 1 →
      Real.log ‖g z‖ ≤ A * ((N : ℝ) + R + 4) * (1 + Real.log ((N : ℝ) + R + 4)) := by
  intro N z hz
  let r : ℝ := (N : ℝ) + R + 2
  let B : ℝ := A * ((N : ℝ) + R + 4) * (1 + Real.log ((N : ℝ) + R + 4))
  have hr : 0 < r := by dsimp [r]; positivity
  have hbd : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ Real.exp B := by
    intro w hw
    have hnw : ‖w‖ = r := by simpa using hw
    have hdist (u : ℂ) (hu : u ∈ S) : 1 ≤ ‖w - u‖ := by
      have hh := norm_le_norm_sub_add w u
      have hsu := hS u hu
      dsimp [r] at hnw
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hp : 1 ≤ ‖finiteZeroPolynomial f S w‖ := by
      rw [finiteZeroPolynomial, norm_prod]
      apply Finset.one_le_prod₀
      intro u hu
      rw [norm_pow]
      exact one_le_pow₀ (hdist u hu)
    have hfn : 0 < ‖f w‖ := by
      rw [he w, norm_mul]
      exact mul_pos (by linarith) (norm_pos_iff.mpr (hne w))
    have hlog := hf (N + R + 1) w (by push_cast; dsimp [r] at hnw; linarith)
    have hlog' : Real.log ‖f w‖ ≤ B := by
      simpa only [Nat.cast_add, Nat.cast_one, B,
        show (N : ℝ) + R + 1 + 3 = (N : ℝ) + R + 4 by ring] using hlog
    calc
      _ ≤ ‖finiteZeroPolynomial f S w‖ * ‖g w‖ := le_mul_of_one_le_left (norm_nonneg _) hp
      _ = ‖f w‖ := by rw [he w, norm_mul]
      _ ≤ Real.exp B := by simpa only [Real.exp_log hfn] using Real.exp_le_exp.mpr hlog'
  have hn : ‖g z‖ ≤ Real.exp B := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
    · exact DiffContOnCl.mk_ball (fun w _ => (hg w).differentiableAt.differentiableWithinAt)
        (fun w _ => (hg w).continuousAt.continuousWithinAt)
    · rwa [frontier_ball 0 hr.ne']
    · rw [closure_ball 0 hr.ne', mem_closedBall, dist_zero_right]
      dsimp [r]
      linarith [Nat.cast_nonneg (α := ℝ) R]
  have hh := Real.log_le_log (norm_pos_iff.mpr (hne z)) hn
  simpa only [Real.log_exp] using hh

end Ostmann

end OAI
