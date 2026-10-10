import OAI.Combinatorics.Progressions.Probability.ScaledArrayLaw

namespace OAI

section

namespace Erdos3

theorem constantChartDensityCap_factorization (a n : ℕ) :
    constantChartDensityCap a n =
      (8 * (probabilityProfileLipschitz : ℝ)) ^ n * (8 * ((a : ℝ) + 1)) ^ (a + n) *
        constantChartDistortion n ^ (a + n + 1) := by
  have hR : (constantChartWidth a n)⁻¹ = (8 * ((a : ℝ) + 1)) * constantChartDistortion n := by
    simp only [constantChartWidth, one_div, inv_inv]
    ring
  rw [constantChartDensityCap, div_eq_mul_inv, hR]
  simp only [mul_pow, pow_add, pow_one]
  ring

noncomputable def constantChartLogBudget (a n : ℕ) : ℝ :=
  (n : ℝ) * (8 * (probabilityProfileLipschitz : ℝ)) +
    ((a : ℝ) + n) * (8 * ((a : ℝ) + 1)) +
    ((a : ℝ) + n + 1) * (20 * ((n : ℝ) + 1) ^ 3)

theorem constantChartDensityCap_le_exp (a n : ℕ) :
    constantChartDensityCap a n ≤ Real.exp (constantChartLogBudget a n) := by
  have hP : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp (8 * (probabilityProfileLipschitz : ℝ)) :=
    by linarith [Real.add_one_le_exp (8 * (probabilityProfileLipschitz : ℝ))]
  have hQ : 8 * ((a : ℝ) + 1) ≤ Real.exp (8 * ((a : ℝ) + 1)) :=
    by linarith [Real.add_one_le_exp (8 * ((a : ℝ) + 1))]
  rw [constantChartDensityCap_factorization, constantChartDistortion]
  calc
    _ ≤ Real.exp (8 * (probabilityProfileLipschitz : ℝ)) ^ n *
        Real.exp (8 * ((a : ℝ) + 1)) ^ (a + n) *
        Real.exp (20 * ((n : ℝ) + 1) ^ 3) ^ (a + n + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [constantChartLogBudget, Nat.cast_add, Nat.cast_one]

theorem constantChartWidth_inv_le_exp (a n : ℕ) :
    (constantChartWidth a n)⁻¹ ≤
      Real.exp (8 * ((a : ℝ) + 1) + 20 * ((n : ℝ) + 1) ^ 3) := by
  have hQ : 8 * ((a : ℝ) + 1) ≤ Real.exp (8 * ((a : ℝ) + 1)) :=
    by linarith [Real.add_one_le_exp (8 * ((a : ℝ) + 1))]
  simp only [constantChartWidth, one_div, inv_inv, constantChartDistortion, Real.exp_add]
  nlinarith [Real.exp_pos (20 * ((n : ℝ) + 1) ^ 3)]

end Erdos3

end

end OAI
