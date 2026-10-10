import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevWeights
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevProductWeights

namespace OAI

/-! # The uniform weight inequality for multiplication in Y_L -/

namespace DefocusingNLS

/-- The positive Fourier weight whose ℓ² norm is exactly the manuscript's `Y_L` norm. -/
noncomputable def expandingSobolevWeight (a k L : ℝ) (n : frequencyLattice) : ℝ :=
  (2 * Real.pi) ^ 6 * Real.sqrt (expandingSobolevWeightSq a k L n)

theorem expandingSobolevWeight_pos (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    0 < expandingSobolevWeight a k L n := by
  unfold expandingSobolevWeight
  exact mul_pos (pow_pos (by positivity) _)
    (Real.sqrt_pos.2 (expandingSobolevWeightSq_pos a k L hL n))

theorem expandingSobolevWeight_sq (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    expandingSobolevWeight a k L n ^ 2 =
      (2 * Real.pi) ^ 12 * expandingSobolevWeightSq a k L n := by
  unfold expandingSobolevWeight
  rw [mul_pow, Real.sq_sqrt (expandingSobolevWeightSq_pos a k L hL n).le, ← pow_mul]

private theorem norm_rpow_add_le (k : ℝ) (hk : 8 < k) (m n : frequencyLattice) :
    ‖m + n‖ ^ (2 * k) ≤ 4 ^ k * (‖m‖ ^ (2 * k) + ‖n‖ ^ (2 * k)) := by
  have hm : ‖m‖ ≤ max ‖m‖ ‖n‖ := le_max_left _ _
  have hn : ‖n‖ ≤ max ‖m‖ ‖n‖ := le_max_right _ _
  have hs : ‖m + n‖ ≤ 2 * max ‖m‖ ‖n‖ := by linarith [norm_add_le m n]
  have he : 0 ≤ 2 * k := by linarith
  calc
    _ ≤ (2 * max ‖m‖ ‖n‖) ^ (2 * k) :=
      Real.rpow_le_rpow (norm_nonneg _) hs he
    _ = 4 ^ k * max (‖m‖ ^ (2 * k)) (‖n‖ ^ (2 * k)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        Real.rpow_max (norm_nonneg _) (norm_nonneg _) he]
      congr 1
      rw [Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_le
      (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity)))
      (by positivity)

/-- The squared weight has an addition constant independent of the growing torus scale. -/
theorem expandingSobolevWeightSq_add_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m n : frequencyLattice) :
    expandingSobolevWeightSq a k L (m + n) ≤
      4 ^ k * (expandingSobolevWeightSq a k L m + expandingSobolevWeightSq a k L n) := by
  have hl := sobolevProductWeight_add_le (2 * (6 - a)) (by linarith) m n
  have hl' : (1 + ‖m + n‖ ^ 2) ^ (6 - a) ≤
      4 ^ (6 - a) * ((1 + ‖m‖ ^ 2) ^ (6 - a) + (1 + ‖n‖ ^ 2) ^ (6 - a)) := by
    have he : 2 * (6 - a) / 2 = 6 - a := by ring
    simpa only [sobolevProductWeight, he] using hl
  have hc : (4 : ℝ) ^ (6 - a) ≤ 4 ^ k :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hl'' : (1 + ‖m + n‖ ^ 2) ^ (6 - a) ≤
      4 ^ k * ((1 + ‖m‖ ^ 2) ^ (6 - a) + (1 + ‖n‖ ^ 2) ^ (6 - a)) :=
    hl'.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  have hh := norm_rpow_add_le k hk m n
  unfold expandingSobolevWeightSq
  calc
    _ ≤ L ^ (2 * a) * (4 ^ k *
        ((1 + ‖m‖ ^ 2) ^ (6 - a) + (1 + ‖n‖ ^ 2) ^ (6 - a))) +
      L ^ (12 - 2 * k) * (4 ^ k * (‖m‖ ^ (2 * k) + ‖n‖ ^ (2 * k))) :=
      add_le_add (mul_le_mul_of_nonneg_left hl'' (by positivity))
        (mul_le_mul_of_nonneg_left hh (by positivity))
    _ = _ := by ring

/-- The exact positive weight satisfies the two-term Young convolution inequality. -/
theorem expandingSobolevWeight_add_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m n : frequencyLattice) :
    expandingSobolevWeight a k L (m + n) ≤
      Real.sqrt (4 ^ k) * (expandingSobolevWeight a k L m + expandingSobolevWeight a k L n) := by
  have h := Real.sqrt_le_sqrt (expandingSobolevWeightSq_add_le a k L ha ha1 hk hL m n)
  rw [Real.sqrt_mul (by positivity)] at h
  have hm := (expandingSobolevWeightSq_pos a k L hL m).le
  have hn := (expandingSobolevWeightSq_pos a k L hL n).le
  have hsum : Real.sqrt (expandingSobolevWeightSq a k L m + expandingSobolevWeightSq a k L n) ≤
      Real.sqrt (expandingSobolevWeightSq a k L m) +
        Real.sqrt (expandingSobolevWeightSq a k L n) := by
    have hms := Real.sq_sqrt hm
    have hns := Real.sq_sqrt hn
    have hss := Real.sq_sqrt (add_nonneg hm hn)
    have hmn := mul_nonneg (Real.sqrt_nonneg (expandingSobolevWeightSq a k L m))
      (Real.sqrt_nonneg (expandingSobolevWeightSq a k L n))
    nlinarith [Real.sqrt_nonneg (expandingSobolevWeightSq a k L m),
      Real.sqrt_nonneg (expandingSobolevWeightSq a k L n),
      Real.sqrt_nonneg (expandingSobolevWeightSq a k L m + expandingSobolevWeightSq a k L n)]
  unfold expandingSobolevWeight
  calc
    _ ≤ (2 * Real.pi) ^ 6 * (Real.sqrt (4 ^ k) *
      Real.sqrt (expandingSobolevWeightSq a k L m + expandingSobolevWeightSq a k L n)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ (2 * Real.pi) ^ 6 * (Real.sqrt (4 ^ k) *
      (Real.sqrt (expandingSobolevWeightSq a k L m) +
        Real.sqrt (expandingSobolevWeightSq a k L n))) := by gcongr
    _ = _ := by ring

end DefocusingNLS

end OAI
