import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMatrixCostEnvelope

namespace OAI

/-! # A common matrix budget for each actual divisor band -/

namespace Ostmann

private theorem root_product_factor {F Y N u v E₁ E₂ : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N)
    (hu : 0 < u) (hv : 0 < v) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    Real.sqrt (2 * (F * (Y + N / u)) * u * E₁) *
      Real.sqrt (2 * (F * (Y + N / v)) * v * E₂) =
      2 * F * Real.sqrt (u * v) *
        (Real.sqrt (Y + N / u) * Real.sqrt (Y + N / v)) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
  have ha : 0 ≤ Y + N / u := by positivity
  have hb : 0 ≤ Y + N / v := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (F * (Y + N / u)) * u * E₁),
    Real.sq_sqrt (by positivity : 0 ≤ 2 * (F * (Y + N / v)) * v * E₂),
    Real.sq_sqrt (mul_nonneg hu.le hv.le), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sq_sqrt hE₁, Real.sq_sqrt hE₂]
  ring

/-- The divisor-product upper cutoff gives one budget independent of the
chosen two divisor blocks. The lower cutoff controls the geometry. -/
theorem quadratic_growth_band_root_bound {F Y N u v D E₁ E₂ : ℝ}
    (hF : 0 ≤ F) (hY : 0 ≤ Y) (hN : 0 ≤ N)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hD : 0 < D)
    (hP : u * v ≤ 2 * D) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) :
    Real.sqrt (2 * (F * (Y + N / u)) * u * E₁) *
      Real.sqrt (2 * (F * (Y + N / v)) * v * E₂) ≤
      8 * F * Real.sqrt D *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hv₀ : 0 < v := zero_lt_one.trans_le hv
  have hsp : Real.sqrt (u * v) ≤ 2 * Real.sqrt D := by
    have hh : u * v ≤ 4 * D := by linarith
    calc
      _ ≤ Real.sqrt (4 * D) := Real.sqrt_le_sqrt hh
      _ = 2 * Real.sqrt D := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hsd : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hsu : Real.sqrt (u * v) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu₀ hv₀)).ne'
  have hp := quadratic_two_scale_sqrt_cost hY hN hu hv
  rw [root_product_factor hF hY hN hu₀ hv₀ hE₁ hE₂]
  calc
    _ ≤ 2 * F * Real.sqrt (u * v) *
        (Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v)) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by gcongr
    _ ≤ 8 * F * Real.sqrt D *
        (Y + Real.sqrt (Y * N) + N / Real.sqrt D) *
          (Real.sqrt E₁ * Real.sqrt E₂) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hy := mul_le_mul_of_nonneg_right hsp hY
      have hc := mul_le_mul_of_nonneg_right hsp (Real.sqrt_nonneg (Y * N))
      have hn := hN
      have hid₁ : Real.sqrt (u * v) * (N / Real.sqrt (u * v)) = N := by field_simp
      have hid₂ : Real.sqrt D * (N / Real.sqrt D) = N := by field_simp
      have hh : Real.sqrt (u * v) *
          (Y + 2 * Real.sqrt (Y * N) + N / Real.sqrt (u * v)) ≤
          4 * Real.sqrt D * (Y + Real.sqrt (Y * N) + N / Real.sqrt D) := by
        rw [mul_add, mul_add, hid₁]
        rw [mul_add, mul_add]
        nlinarith [mul_nonneg (Real.sqrt_nonneg D) hY]
      nlinarith [mul_le_mul_of_nonneg_left hh hF]

end Ostmann

end OAI
