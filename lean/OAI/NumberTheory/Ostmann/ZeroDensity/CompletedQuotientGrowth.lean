import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedDiskGrowthRate
import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeDiskOscillation

namespace OAI

/-! # Uniform normalized growth of the actual zero-removed quotients -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem completed_quotient_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ g : ℂ → ℂ,
      (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, χ.completed z =
        finiteZeroPolynomial χ.completed (completedDiskZeros χ ((n : ℝ) + 1)) z * g z) ∧
      (∀ z ∈ closedBall (0 : ℂ) (2 * ((n : ℝ) + 1)), g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) (2 * ((n : ℝ) + 1)),
        Real.log ‖g z‖ - Real.log ‖g 0‖ ≤
          C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) +
            |Real.log ‖χ.completed 0‖| + 1) := by
  obtain ⟨U, hU, hf⟩ := completed_circle_log_growth χ
  obtain ⟨V, hV, hmass⟩ := completed_disk_mass_log_growth χ
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨U + V * Real.log 2 + 1, by positivity, ?_⟩
  intro n
  let R : ℝ := (n : ℝ) + 1
  let B : ℝ := ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9))
  let M : ℝ := Real.exp (U * B)
  have hR : 0 < R := by dsimp [R]; positivity
  have hB : 0 < B := by
    have hh : 0 ≤ Real.log ((n : ℝ) + 9) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [B]
    positivity
  have hM : 0 < M := Real.exp_pos _
  have hf0 : χ.completed 0 ≠ 0 := χ.completed_ne_zero_left 0 (by simp)
  obtain ⟨g, hg, he, hne⟩ := completed_disk_quotient_exists χ R
  refine ⟨g, hg, he, hne, ?_⟩
  intro z hz
  have hfM : ∀ w ∈ sphere (0 : ℂ) (3 * R), ‖χ.completed w‖ ≤ M := by
    intro w hw
    have hwn : ‖w‖ = 3 * R := by simpa using hw
    have hh := hf n w (by change ‖w‖ ≤ 3 * R; exact hwn.le)
    apply (Real.le_exp_log ‖χ.completed w‖).trans
    apply Real.exp_le_exp.mpr
    simpa only [B, mul_assoc] using hh
  have hb := finite_zero_quotient_normalized_log χ.completed g (completedDiskZeros χ R)
    R M hR hM hf0 (fun w hw => ((mem_completedDiskZeros χ R w).mp hw).1) hg he
    hfM z (ball_subset_closedBall hz) (hne z (ball_subset_closedBall hz))
  have hm := mul_le_mul_of_nonneg_right (hmass n) hl2
  dsimp only [M] at hb
  rw [Real.log_exp] at hb
  dsimp only [R, B] at hb
  nlinarith [neg_le_abs (Real.log ‖χ.completed 0‖)]

end Ostmann

end OAI
