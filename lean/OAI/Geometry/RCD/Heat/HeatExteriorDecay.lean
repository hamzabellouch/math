import OAI.Geometry.RCD.Heat.GaussianMassEnvelope

namespace OAI

/-! # Geometric decay of the exterior term in the actual heat increment -/

noncomputable section

namespace RegularPointCoordinates

/-- The Gaussian shell factor decreases with the outward shell index. -/
theorem gaussianShellFactor_succ_le {c : ℝ} (hc : 0 ≤ c) (j : ℕ) :
    gaussianShellFactor c (j + 1) ≤ gaussianShellFactor c j := by
  cases j with
  | zero =>
    simp only [gaussianShellFactor, pow_zero]
    exact Real.exp_le_one_iff.mpr (by linarith)
  | succ j =>
    simp only [gaussianShellFactor]
    apply Real.exp_le_exp.mpr
    have hp : (4 : ℝ) ^ j ≤ 4 ^ (j + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ j)
    nlinarith

/-- The exterior Gaussian uses the next shell and thus satisfies the
same fixed geometric coefficient bound. -/
theorem gaussian_exterior_coefficient_le (m : ℕ) {D : ℝ} (hD : 0 < D) (j : ℕ) :
    ((2 : ℝ) ^ m) ^ j * Real.exp (-(4 : ℝ) ^ j / D) ≤
      gaussianMassConvolutionConstant m D⁻¹ * (3 / 4 : ℝ) ^ j := by
  have he : Real.exp (-(4 : ℝ) ^ j / D) = gaussianShellFactor D⁻¹ (j + 1) := by
    simp only [gaussianShellFactor, div_eq_mul_inv, neg_mul]
    congr 1
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left (gaussianShellFactor_succ_le (inv_pos.mpr hD).le j)
    (by positivity)).trans (gaussian_mass_coefficient_le m (inv_pos.mpr hD) j)

/-- A fixed outer radius converts the exterior source term into a
geometrically decaying background term, with no residual inverse fine scale. -/
theorem heat_exterior_term_le_geometric (m N : ℕ) {s R A D M : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hD : 0 < D) (hM : 0 ≤ M)
    (hR : (2 : ℝ) ^ N * s = R) :
    s ^ 2 * ((A / s ^ (m + 2)) * Real.exp (-(4 : ℝ) ^ N / D)) * M ≤
      (A * gaussianMassConvolutionConstant m D⁻¹ * (R ^ 2 / R ^ (m + 2)) * M) *
        (3 / 4 : ℝ) ^ N := by
  have hRpos : 0 < R := hR ▸ mul_pos (by positivity) hs
  have hscale := scaled_mass_dyadic_identity m N hs M
  rw [hR] at hscale
  have hcoef := gaussian_exterior_coefficient_le m hD N
  have hfactor : 0 ≤ A * ((R ^ 2 / R ^ (m + 2)) * M) := by positivity
  have hb := mul_le_mul_of_nonneg_left hcoef hfactor
  calc
    _ = (A * Real.exp (-(4 : ℝ) ^ N / D)) * ((s ^ 2 / s ^ (m + 2)) * M) := by ring
    _ = _ := by rw [hscale]
    _ ≤ _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

end RegularPointCoordinates

end

end OAI
