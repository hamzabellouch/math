import OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierSwitching

namespace OAI

/-! A polynomial degree bound and exponential Fourier error, with no
analytic parameter hypotheses left over from the switching argument. -/

namespace TwoPointCorrelations

open scoped Classical

def switchingDenominator (r : ℕ) : ℕ := 24 * (2 * r + 3) ^ 2

def switchingDegree (d r : ℕ) : ℕ := 8 * (r + 1) * switchingDenominator r ^ d

lemma switchingDenominator_pos (r : ℕ) : 0 < switchingDenominator r := by
  unfold switchingDenominator
  positivity

theorem AC0Circuit.fourier_tail_polynomial_degree {n : ℕ} (c : AC0Circuit n)
    (d r : ℕ) (hc : c.depth ≤ d) (hr : 1 ≤ r) :
    cubeAverage (fun x => (c.indicator x -
      walshTruncation c.indicator (switchingDegree d r) x) ^ 2) ≤
      4 * (c.size : ℝ) * (1 / 2 : ℝ) ^ (r + 1) := by
  let R : ℝ := switchingDenominator r
  let p : ℝ := 1 / R
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast switchingDenominator_pos r
  have hR2 : 2 ≤ R := by
    dsimp [R, switchingDenominator]
    push_cast
    nlinarith [sq_nonneg (2 * (r : ℝ) + 2), show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hphalf : p ≤ 1 / 2 := by
    dsimp [p]
    exact (div_le_div_iff₀ hR (by norm_num)).mpr (by linarith)
  have hp1 : p < 1 := lt_of_le_of_lt hphalf (by norm_num)
  have hRp : R * p = 1 := by dsimp [p]; field_simp
  have hA : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * 8 = R := by
    dsimp [R, switchingDenominator]
    push_cast
    ring
  have hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 1 - p by linarith)).mpr
    rw [← hA] at hRp
    nlinarith [hRp]
  have hmain : p ^ d * (switchingDegree d r : ℝ) = 8 * (r + 1 : ℝ) := by
    dsimp [switchingDegree, p, R]
    push_cast
    field_simp [ne_of_gt (show (0 : ℝ) < switchingDenominator r from hR)]
    rw [← mul_pow]
    simp [ne_of_gt (show (0 : ℝ) < switchingDenominator r from hR)]
  have hprod : 8 * (r + 1 : ℝ) ≤ p ^ d * ((switchingDegree d r : ℝ) + 1) := by
    calc
      _ = p ^ d * (switchingDegree d r : ℝ) := hmain.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hp _)
  have hh := c.fourier_tail_switching p hp hp1 r hr hq d (switchingDegree d r) hc
    (by nlinarith [show (0 : ℝ) ≤ r by positivity]) (by linarith)
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _)
    (by positivity)

end TwoPointCorrelations

end OAI
