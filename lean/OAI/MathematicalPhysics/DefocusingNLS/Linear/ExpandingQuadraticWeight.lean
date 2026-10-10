import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalQuadraticWeight

namespace OAI

/-! # The physical Laplacian multiplier between adjacent expanding norms -/

namespace DefocusingNLS

theorem expandingSobolevWeight_quadratic (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    (‖n‖ / L) ^ 2 * expandingSobolevWeight a k L n ≤
      Real.sqrt (2 ^ (6 - a) + 1) * expandingSobolevWeight a (k + 2) L n := by
  have hLp : 0 < L := by linarith
  have hx : 0 ≤ L ^ (-2 : ℝ) := Real.rpow_nonneg hLp.le _
  have hx1 : L ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
  have h := physical_quadratic_weight a k (L ^ (-2 : ℝ)) (‖n‖ / L) ha ha1 hk hx hx1
    (div_nonneg (norm_nonneg _) hLp.le)
  have hw (j : ℝ) : expandingSobolevWeight a j L n ^ 2 =
      (2 * Real.pi * L) ^ 12 * ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * j)) := by
    rw [expandingSobolevWeight_sq a j L hL]
    exact (expandingSobolevWeightSq_original a j L hL n).symm
  have hsq : ((‖n‖ / L) ^ 2 * expandingSobolevWeight a k L n) ^ 2 ≤
      (Real.sqrt (2 ^ (6 - a) + 1) * expandingSobolevWeight a (k + 2) L n) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hw k, hw (k + 2)]
    have hd := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 * Real.pi * L) ^ 12 by positivity)
    nlinarith
  have hl : 0 ≤ (‖n‖ / L) ^ 2 * expandingSobolevWeight a k L n := by
    exact mul_nonneg (sq_nonneg _) (expandingSobolevWeight_pos a k L hL n).le
  have hr : 0 ≤ Real.sqrt (2 ^ (6 - a) + 1) * expandingSobolevWeight a (k + 2) L n :=
    mul_nonneg (Real.sqrt_nonneg _) (expandingSobolevWeight_pos a (k + 2) L hL n).le
  nlinarith

end DefocusingNLS

end OAI
