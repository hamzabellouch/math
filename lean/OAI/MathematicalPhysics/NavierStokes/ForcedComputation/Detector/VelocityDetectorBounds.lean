import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDetectorScales
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Effective exponential and support-width bounds for each detector burst. -/

namespace ForcedComputation.VelocityDetector

theorem exp_coefficient_le_expansion (L : ℕ) :
    Real.exp (L : ℝ) ≤ (expansion L : ℝ) := by
  have he : Real.exp (1 : ℝ) ≤ 4 := (Real.exp_one_lt_three.trans (by norm_num)).le
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he L
  simpa only [expansion, Nat.cast_pow, Nat.cast_ofNat, ← Real.exp_nat_mul, mul_one] using hp

theorem exp_time_le_expansion_pow (L n : ℕ) {s : ℝ} (hs : s ≤ n) :
    Real.exp ((L : ℝ) * s) ≤ (expansion L : ℝ) ^ n := by
  calc
    _ ≤ Real.exp ((L : ℝ) * n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg L))
    _ = Real.exp (L : ℝ) ^ n := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (exp_coefficient_le_expansion L) n

theorem transported_width (L n : ℕ) :
    width L n * (expansion L : ℚ) ^ (n + 1) =
      (1 / 1000000) * (1 / 2) ^ (n + 1) := by
  have hR : (expansion L : ℚ) ≠ 0 := by
    exact_mod_cast (expansion_pos L).ne'
  have hb : geometricRatio L * (expansion L : ℚ) = 1 / 2 := by
    unfold geometricRatio
    field_simp [hR]
  calc
    _ = (1 / 1000000) * (geometricRatio L * (expansion L : ℚ)) ^ (n + 1) := by
      rw [mul_pow]
      exact mul_assoc _ _ _
    _ = _ := by rw [hb]

end ForcedComputation.VelocityDetector

end OAI
