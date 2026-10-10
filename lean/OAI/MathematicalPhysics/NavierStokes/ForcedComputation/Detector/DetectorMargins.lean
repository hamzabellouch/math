import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDetectorScales

namespace OAI

/-! Numerical margins shared by the two published detector clearances. -/

namespace ForcedComputation.VelocityDetector

theorem massBound_real_small (L : ℕ) :
    0 ≤ (massBound L : ℝ) ∧ (massBound L : ℝ) < 1 / 100000000000 := by
  constructor
  · exact_mod_cast (massBound_small L).1
  · have h := (Rat.cast_lt (K := ℝ)).mpr (massBound_small L).2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    exact h

theorem detector_old_mass_margin (L : ℕ) :
    (16 : ℝ) * (massBound L : ℝ) < 1 / 16 := by
  have h := (massBound_real_small L).2
  linarith

theorem detector_wait_margin (L : ℕ) {H : ℝ} (hH : H ≤ 1000000000) :
    H * (massBound L : ℝ) + (16 * (massBound L : ℝ) + 1 / 16) < 1 / 2 := by
  have hm := massBound_real_small L
  have hh := mul_le_mul_of_nonneg_right hH hm.1
  nlinarith

end ForcedComputation.VelocityDetector

end OAI
