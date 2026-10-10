import OAI.Geometry.RCD.Heat.GaussianShellKernel

namespace OAI

/-! # Global exponential volume growth is absorbed by Gaussian decay -/

open Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

/-- Completing the square leaves half of the Gaussian exponent available. -/
theorem linear_sub_quadratic_le (A s : ℝ) {c : ℝ} (hc : 0 < c) :
    A * s - c * s ^ 2 ≤ A ^ 2 / (2 * c) - (c / 2) * s ^ 2 := by
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * c by positivity)).mp
  have he : (A ^ 2 / (2 * c) - c / 2 * s ^ 2) * (2 * c) = A ^ 2 - c ^ 2 * s ^ 2 := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg (c * s - A)]

/-- A fixed exponential volume factor in the shell radius does not spoil
summability of any geometric normalization loss. -/
theorem summable_gaussian_with_linear_growth {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (A : ℝ) :
    Summable (fun j : ℕ => b ^ j * Real.exp (A * 2 ^ j - c * 4 ^ j)) := by
  have hs := (summable_dyadic_gaussian hb (half_pos hc) (by norm_num : (1 : ℝ) < 4)).mul_left
    (Real.exp (A ^ 2 / (2 * c)))
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro j
  have hp : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [pow_two, ← mul_pow]; norm_num
  have he := linear_sub_quadratic_le A ((2 : ℝ) ^ j) hc
  rw [hp] at he
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (pow_nonneg hb j)
  have hrhs : Real.exp (A ^ 2 / (2 * c) - c / 2 * 4 ^ j) =
      Real.exp (A ^ 2 / (2 * c)) * Real.exp (-(c / 2) * 4 ^ j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrhs] at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

/-- The first shell includes the pole; all later shells still allow a
global hyperbolic exponential factor in their radius. -/
theorem summable_shell_with_linear_growth {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (A : ℝ) :
    Summable (fun j : ℕ => b ^ j * Real.exp (A * 2 ^ j) * gaussianShellFactor c j) := by
  rw [← summable_nat_add_iff 1]
  have hs := (summable_gaussian_with_linear_growth hb hc (2 * A)).mul_left b
  apply hs.congr
  intro j
  simp only [gaussianShellFactor, pow_succ]
  rw [show (2 * A) * (2 : ℝ) ^ j - c * 4 ^ j = A * (2 ^ j * 2) + -c * 4 ^ j by ring,
    Real.exp_add]
  ring

end RegularPointCoordinates

end

end OAI
