import OAI.Geometry.RCD.Heat.GaussianShellKernel

namespace OAI

/-! # Geometric envelopes for the finite Gaussian mass convolution -/

open scoped BigOperators

noncomputable section

namespace RegularPointCoordinates

/-- The fixed three-quarter decay is compatible with the proved slow
inverse growth, and dominates every Gaussian shell coefficient. -/
def gaussianMassConvolutionConstant (m : ℕ) (c : ℝ) : ℝ :=
  ∑' j : ℕ, (((2 : ℝ) ^ m) / (3 / 4)) ^ j * gaussianShellFactor c j

theorem gaussianMassConvolutionConstant_nonneg (m : ℕ) (c : ℝ) :
    0 ≤ gaussianMassConvolutionConstant m c := by
  apply tsum_nonneg
  intro j
  exact mul_nonneg (by positivity) (gaussianShellFactor_nonneg c j)

/-- The dimension is m+2, so the scaled mass costs 2^(m j) on the jth
outward shell. The remaining Gaussian gives a uniform geometric kernel. -/
theorem gaussian_mass_coefficient_le (m : ℕ) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ((2 : ℝ) ^ m) ^ j * gaussianShellFactor c j ≤
      gaussianMassConvolutionConstant m c * (3 / 4 : ℝ) ^ j := by
  have hs := summable_gaussianShellFactor
    (show 0 ≤ ((2 : ℝ) ^ m) / (3 / 4) by positivity) hc
  have hterm : (((2 : ℝ) ^ m) / (3 / 4)) ^ j * gaussianShellFactor c j ≤
      gaussianMassConvolutionConstant m c :=
    hs.le_tsum j (fun k _ => mul_nonneg (by positivity) (gaussianShellFactor_nonneg c k))
  have hm := mul_le_mul_of_nonneg_right hterm (by positivity : 0 ≤ (3 / 4 : ℝ) ^ j)
  calc
    _ = ((((2 : ℝ) ^ m) / (3 / 4)) ^ j * gaussianShellFactor c j) * (3 / 4 : ℝ) ^ j := by
      rw [div_pow]
      field_simp
    _ ≤ _ := hm

/-- Exact cancellation of the scale factors in a dimension m+2 mass. -/
theorem scaled_mass_dyadic_identity (m j : ℕ) {r : ℝ} (hr : 0 < r) (v : ℝ) :
    (r ^ 2 / r ^ (m + 2)) * v =
      ((2 : ℝ) ^ m) ^ j * (((2 ^ j * r) ^ 2 / (2 ^ j * r) ^ (m + 2)) * v) := by
  rw [pow_add, pow_add, mul_pow, mul_pow, pow_right_comm (2 : ℝ) j m]
  field_simp

end RegularPointCoordinates

end

end OAI
