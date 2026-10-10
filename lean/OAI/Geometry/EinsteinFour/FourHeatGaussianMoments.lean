import OAI.Geometry.EinsteinFour.FourHeatGaussian

namespace OAI

/-! Polynomial absorption and actual Gaussian moment bounds for the local
heat remainder. These bounds use Euclidean volume and the proved unit mass. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

theorem fourHeatGaussian_half_exponent (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    fourHeatGaussian t x =
      4 * Real.exp (-(8 * t)⁻¹ * ‖x‖ ^ 2) * fourHeatGaussian (2 * t) x := by
  have h8 : 4 * (2 * t) = 8 * t := by ring
  have he : -(4 * t)⁻¹ * ‖x‖ ^ 2 =
      -(8 * t)⁻¹ * ‖x‖ ^ 2 + -(8 * t)⁻¹ * ‖x‖ ^ 2 := by
    field_simp
    ring
  unfold fourHeatGaussian
  rw [h8, he, Real.exp_add]
  field_simp [Real.pi_ne_zero]
  ring

theorem fourHeatPolynomial_absorption (m : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    z ^ m * Real.exp (-z) ≤ (m.factorial : ℝ) := by
  have hf : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have h : z ^ m ≤ Real.exp z * (m.factorial : ℝ) :=
    (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp z hz m)
  calc
    _ ≤ (Real.exp z * (m.factorial : ℝ)) * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
      rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

theorem fourHeatGaussian_moment_bound (m : ℕ) (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    ‖x‖ ^ (2 * m) * fourHeatGaussian t x ≤
      (4 * (m.factorial : ℝ) * (8 * t) ^ m) * fourHeatGaussian (2 * t) x := by
  let z := ‖x‖ ^ 2 / (8 * t)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have he : -(8 * t)⁻¹ * ‖x‖ ^ 2 = -z := by dsimp [z]; ring
  have hp : ‖x‖ ^ (2 * m) = (8 * t) ^ m * z ^ m := by
    dsimp [z]
    rw [div_pow, ← pow_mul]
    field_simp
  rw [fourHeatGaussian_half_exponent t ht, he, hp]
  have h := mul_le_mul_of_nonneg_left (fourHeatPolynomial_absorption m z hz)
    (show 0 ≤ 4 * (8 * t) ^ m * fourHeatGaussian (2 * t) x by
      exact mul_nonneg (by positivity) (fourHeatGaussian_pos _ (by positivity) x).le)
  convert h using 1 <;> ring

theorem fourHeatGaussian_moment_integrable (m : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : FourSpace => ‖x‖ ^ (2 * m) * fourHeatGaussian t x) := by
  have hmajor := (fourHeatGaussian_integrable (2 * t) (by positivity)).const_mul
    (4 * (m.factorial : ℝ) * (8 * t) ^ m)
  have hm : AEStronglyMeasurable
      (fun x : FourSpace => ‖x‖ ^ (2 * m) * fourHeatGaussian t x) volume :=
    ((continuous_norm.pow _).mul (fourHeatGaussian_continuous t)).aestronglyMeasurable
  exact hmajor.mono_nonneg hm
    (Filter.Eventually.of_forall fun x =>
      mul_nonneg (by positivity) (fourHeatGaussian_pos t ht x).le)
    (Filter.Eventually.of_forall (fourHeatGaussian_moment_bound m t ht))

theorem fourHeatGaussian_integral_moment_bound (m : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, ‖x‖ ^ (2 * m) * fourHeatGaussian t x) ≤
      4 * (m.factorial : ℝ) * (8 * t) ^ m := by
  calc
    _ ≤ ∫ x : FourSpace,
        (4 * (m.factorial : ℝ) * (8 * t) ^ m) * fourHeatGaussian (2 * t) x :=
      integral_mono (fourHeatGaussian_moment_integrable m t ht)
        ((fourHeatGaussian_integrable (2 * t) (by positivity)).const_mul _)
        (fourHeatGaussian_moment_bound m t ht)
    _ = _ := by
      rw [integral_const_mul, fourHeatGaussian_mass (2 * t) (by positivity), mul_one]

end
end PositiveEinsteinFour.Geometry

end OAI
