import OAI.Geometry.EinsteinFour.RadialIntegrals
import OAI.Geometry.EinsteinFour.RadialCoefficient

namespace OAI

/-! Integration of the radial determinant deficit using the radial
comparison and polar volume formula. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory

noncomputable section

theorem integral_sine_cube :
    (∫ u in (0 : ℝ)..1, Real.sin (Real.pi * u) ^ 3) = 4 / (3 * Real.pi) := by
  have hd (u : ℝ) : HasDerivAt
      (fun z => -Real.cos (Real.pi * z) / Real.pi +
        Real.cos (Real.pi * z) ^ 3 / (3 * Real.pi))
      (Real.sin (Real.pi * u) ^ 3) u := by
    have hc := ((hasDerivAt_id u).const_mul Real.pi).cos
    convert (hc.neg.div_const Real.pi).add
      ((hc.pow 3).div_const (3 * Real.pi)) using 1
    · rfl
    · simp only [id_eq]
      field_simp [Real.pi_ne_zero]
      norm_num only [Nat.reduceSub, Nat.cast_ofNat]
      linear_combination 3 * Real.sin (Real.pi * u) *
        Real.sin_sq_add_cos_sq (Real.pi * u)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [Real.cos_pi]
  ring

/-- Averaging the pointwise determinant loss uses only its nonnegative
coefficient and the lower bound for the averaged squared curvature. -/
theorem radial_deficit_from_average {D Q F s u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hF : 0 ≤ F)
    (hloss : D ≤ Real.sin (Real.pi * u) ^ 3 * (1 - F * Q / 6))
    (hQ : (3 / 2) * s * (1 - u ^ 2 / 2) ≤ Q) :
    D ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - F * s * (1 - u ^ 2 / 2) / 4) := by
  have hsin : 0 ≤ Real.sin (Real.pi * u) := Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le hu) (by nlinarith [Real.pi_pos])
  have hmul := mul_le_mul_of_nonneg_left hQ hF
  have hscaled := mul_le_mul_of_nonneg_left hmul (pow_nonneg hsin 3)
  nlinarith [hloss]

/-- Integration of the radial comparison and polar volume bound gives
equation (7), with coefficient `3/40` from exact rational integration. -/
theorem volume_ratio_upper_of_radial_comparison {D : ℝ → ℝ} {V s : ℝ}
    (hs : 0 ≤ s)
    (hD0 : IntervalIntegrable D volume 0 (5 / 8))
    (hD1 : IntervalIntegrable D volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), D u) + ∫ u in (5 / 8 : ℝ)..1, D u))
    (hfirst : ∀ u ∈ Set.Icc (0 : ℝ) (5 / 8),
      D u ≤ Real.sin (Real.pi * u) ^ 3 - (4 / (3 * Real.pi)) * s * upperKernel u)
    (hlast : ∀ u ∈ Set.Icc (5 / 8 : ℝ) 1,
      D u ≤ Real.sin (Real.pi * u) ^ 3 - (4 / (3 * Real.pi)) * s * upperKernelEnd u) :
    V ≤ 1 - (3 / 40) * s := by
  have hsin0 : IntervalIntegrable (fun u => Real.sin (Real.pi * u) ^ 3)
      volume 0 (5 / 8) := by apply Continuous.intervalIntegrable; fun_prop
  have hsin1 : IntervalIntegrable (fun u => Real.sin (Real.pi * u) ^ 3)
      volume (5 / 8) 1 := by apply Continuous.intervalIntegrable; fun_prop
  have hk0 : IntervalIntegrable upperKernel volume 0 (5 / 8) := by
    apply Continuous.intervalIntegrable
    unfold upperKernel initialFactor
    fun_prop
  have hk1 : IntervalIntegrable upperKernelEnd volume (5 / 8) 1 := by
    apply Continuous.intervalIntegrable
    unfold upperKernelEnd
    fun_prop
  have h0 := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 5 / 8)
    hD0 (hsin0.sub (hk0.const_mul ((4 / (3 * Real.pi)) * s))) hfirst
  have h1 := intervalIntegral.integral_mono_on (by norm_num : (5 / 8 : ℝ) ≤ 1)
    hD1 (hsin1.sub (hk1.const_mul ((4 / (3 * Real.pi)) * s))) hlast
  rw [intervalIntegral.integral_sub hsin0 (hk0.const_mul _),
    intervalIntegral.integral_const_mul] at h0
  rw [intervalIntegral.integral_sub hsin1 (hk1.const_mul _),
    intervalIntegral.integral_const_mul] at h1
  have hsum := intervalIntegral.integral_add_adjacent_intervals hsin0 hsin1
  rw [integral_sine_cube] at hsum
  have hnormalize : (3 * Real.pi / 4) * (4 / (3 * Real.pi)) = 1 := by
    field_simp [Real.pi_ne_zero]
  have hb := mul_le_mul_of_nonneg_left (add_le_add h0 h1)
    (show 0 ≤ 3 * Real.pi / 4 by positivity)
  have hmargin := mul_le_mul_of_nonneg_left analytic_upper_margin.le hs
  have hidentity (a b c d : ℝ) :
      (3 * Real.pi / 4) * ((a - (4 / (3 * Real.pi)) * s * b) +
        (c - (4 / (3 * Real.pi)) * s * d)) =
      (3 * Real.pi / 4) * (a + c) -
        ((3 * Real.pi / 4) * (4 / (3 * Real.pi))) * s * (b + d) := by ring
  rw [hidentity, hsum, hnormalize] at hb
  linarith only [hpolar, hb, hmargin]

/-- Endpoint values have no effect on the volume integral. This form only
requires the radial estimate on the open comparison intervals. -/
theorem volume_ratio_upper_of_radial_comparison_open {D : ℝ → ℝ} {V s : ℝ}
    (hs : 0 ≤ s)
    (hD0 : IntervalIntegrable D volume 0 (5 / 8))
    (hD1 : IntervalIntegrable D volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), D u) + ∫ u in (5 / 8 : ℝ)..1, D u))
    (hfirst : ∀ u ∈ Set.Ioo (0 : ℝ) (5 / 8),
      D u ≤ Real.sin (Real.pi * u) ^ 3 - (4 / (3 * Real.pi)) * s * upperKernel u)
    (hlast : ∀ u ∈ Set.Ioo (5 / 8 : ℝ) 1,
      D u ≤ Real.sin (Real.pi * u) ^ 3 - (4 / (3 * Real.pi)) * s * upperKernelEnd u) :
    V ≤ 1 - (3 / 40) * s := by
  have hsin0 : IntervalIntegrable (fun u => Real.sin (Real.pi * u) ^ 3)
      volume 0 (5 / 8) := by apply Continuous.intervalIntegrable; fun_prop
  have hsin1 : IntervalIntegrable (fun u => Real.sin (Real.pi * u) ^ 3)
      volume (5 / 8) 1 := by apply Continuous.intervalIntegrable; fun_prop
  have hk0 : IntervalIntegrable upperKernel volume 0 (5 / 8) := by
    apply Continuous.intervalIntegrable
    unfold upperKernel initialFactor
    fun_prop
  have hk1 : IntervalIntegrable upperKernelEnd volume (5 / 8) 1 := by
    apply Continuous.intervalIntegrable
    unfold upperKernelEnd
    fun_prop
  have h0 := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 5 / 8)
    hD0 (hsin0.sub (hk0.const_mul ((4 / (3 * Real.pi)) * s))) hfirst
  have h1 := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (5 / 8 : ℝ) ≤ 1)
    hD1 (hsin1.sub (hk1.const_mul ((4 / (3 * Real.pi)) * s))) hlast
  rw [intervalIntegral.integral_sub hsin0 (hk0.const_mul _),
    intervalIntegral.integral_const_mul] at h0
  rw [intervalIntegral.integral_sub hsin1 (hk1.const_mul _),
    intervalIntegral.integral_const_mul] at h1
  have hsum := intervalIntegral.integral_add_adjacent_intervals hsin0 hsin1
  rw [integral_sine_cube] at hsum
  have hnormalize : (3 * Real.pi / 4) * (4 / (3 * Real.pi)) = 1 := by
    field_simp [Real.pi_ne_zero]
  have hb := mul_le_mul_of_nonneg_left (add_le_add h0 h1)
    (show 0 ≤ 3 * Real.pi / 4 by positivity)
  have hmargin := mul_le_mul_of_nonneg_left analytic_upper_margin.le hs
  have hidentity (a b c d : ℝ) :
      (3 * Real.pi / 4) * ((a - (4 / (3 * Real.pi)) * s * b) +
        (c - (4 / (3 * Real.pi)) * s * d)) =
      (3 * Real.pi / 4) * (a + c) -
        ((3 * Real.pi / 4) * (4 / (3 * Real.pi))) * s * (b + d) := by ring
  rw [hidentity, hsum, hnormalize] at hb
  linarith only [hpolar, hb, hmargin]


end

end PositiveEinsteinFour.VolumeConstants

end OAI
