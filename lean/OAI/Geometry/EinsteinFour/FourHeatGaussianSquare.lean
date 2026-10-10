import OAI.Geometry.EinsteinFour.FourHeatGaussianConvolution

namespace OAI

/-! Exact L2 mass of the four-dimensional heat Gaussian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_square_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : FourSpace => fourHeatGaussian t x ^ 2) := by
  have h := fourHeatGaussian_product_integrable t t ht ht 0
  simpa only [fourHeatGaussian, zero_sub, norm_neg, pow_two] using h

theorem fourHeatGaussian_square_mass (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, fourHeatGaussian t x ^ 2) = 1 / (64 * Real.pi ^ 2 * t ^ 2) := by
  have h := fourHeatGaussian_convolution t t ht ht 0
  have he : (fun x : FourSpace => fourHeatGaussian t (0 - x) * fourHeatGaussian t x) =
      (fun x => fourHeatGaussian t x ^ 2) := by
    funext x
    simp only [fourHeatGaussian, zero_sub, norm_neg, pow_two]
  rw [he] at h
  rw [h, fourHeatGaussian]
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
