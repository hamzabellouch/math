import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevWeights

namespace OAI

/-! # The weight inequality needed for multiplication in the Sobolev Fourier model -/

namespace DefocusingNLS

/-- The positive Sobolev weight, inverse to the coefficient normalization. -/
noncomputable def sobolevProductWeight (k : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k / 2)

theorem sobolevProductWeight_pos (k : ℝ) (n : frequencyLattice) :
    0 < sobolevProductWeight k n := Real.rpow_pos_of_pos (by positivity) _

/-- A frequency sum costs at most a fixed multiple of either input weight. -/
theorem sobolevProductWeight_add_le (k : ℝ) (hk : 0 ≤ k) (m n : frequencyLattice) :
    sobolevProductWeight k (m + n) ≤ 4 ^ (k / 2) *
      (sobolevProductWeight k m + sobolevProductWeight k n) := by
  have hsq : ‖m + n‖ ^ 2 ≤ 2 * ‖m‖ ^ 2 + 2 * ‖n‖ ^ 2 := by
    have h := norm_add_le m n
    have hp := sq_nonneg (‖m‖ - ‖n‖)
    nlinarith [norm_nonneg (m + n), norm_nonneg m, norm_nonneg n]
  have hm : 1 + ‖m‖ ^ 2 ≤ max (1 + ‖m‖ ^ 2) (1 + ‖n‖ ^ 2) := le_max_left _ _
  have hn : 1 + ‖n‖ ^ 2 ≤ max (1 + ‖m‖ ^ 2) (1 + ‖n‖ ^ 2) := le_max_right _ _
  have hb : 1 + ‖m + n‖ ^ 2 ≤ 4 * max (1 + ‖m‖ ^ 2) (1 + ‖n‖ ^ 2) := by
    linarith
  have he : 0 ≤ k / 2 := by positivity
  unfold sobolevProductWeight
  calc
    _ ≤ (4 * max (1 + ‖m‖ ^ 2) (1 + ‖n‖ ^ 2)) ^ (k / 2) :=
      Real.rpow_le_rpow (by positivity) hb he
    _ = 4 ^ (k / 2) * max ((1 + ‖m‖ ^ 2) ^ (k / 2))
        ((1 + ‖n‖ ^ 2) ^ (k / 2)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_max (by positivity) (by positivity) he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_le
      (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
      (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))) (by positivity)

end DefocusingNLS

end OAI
