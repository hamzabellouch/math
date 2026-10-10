import OAI.NumberTheory.Ostmann.QuadraticCenter.CutoffBounds

namespace OAI

namespace Ostmann.QuadraticCenter

theorem inv_scale_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
  have hxy : 1 ≤ x * y := one_le_mul_of_one_le_of_one_le hx hy
  nlinarith [mul_nonneg (abs_nonneg (x - y)) (sub_nonneg.mpr hxy)]

theorem sqrt_scale_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have hxs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hys : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have he : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x), Real.sq_sqrt (by linarith : 0 ≤ y)]
  have ha := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x + Real.sqrt y)] at ha
  nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]

theorem inv_sqrt_scale_lipschitz {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |(Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹| ≤ |x - y| := by
  have hxs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hys : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  exact (inv_scale_lipschitz hxs hys).trans (sqrt_scale_lipschitz hx hy)

theorem cutoff_div_scale_lipschitz {R R' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R') (a : ℝ) :
    ‖cutoffFourier (a / R) - cutoffFourier (a / R')‖ ≤
      cutoffFourierBound * |a| * |R - R'| := by
  have h := cutoff_fourier_lipschitz (a / R) (a / R')
  have he : |a / R - a / R'| = |a| * |R⁻¹ - R'⁻¹| := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul]
  rw [he] at h
  calc
    _ ≤ cutoffFourierBound * (|a| * |R⁻¹ - R'⁻¹|) := h
    _ ≤ cutoffFourierBound * (|a| * |R - R'|) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (inv_scale_lipschitz hR hR') (abs_nonneg a)) cutoffFourierBound_pos.le
    _ = _ := by ring

end Ostmann.QuadraticCenter

end OAI
