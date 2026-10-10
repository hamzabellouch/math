import OAI.Geometry.EinsteinFour.AveragedRadial
import OAI.Geometry.EinsteinFour.VolumeAssembly

namespace OAI

/-! The volume deficit follows from the averaged Jacobi bound and the polar
volume formula. All numerical constants and integration weights are proved. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory VolumeConstants

noncomputable section

/-- Replace the exact determinant coefficient by the explicit integrable
piecewise lower bound used in the volume estimate. -/
theorem averaged_radial_piecewise_bound {D s u : ℝ}
    (hu : 0 ≤ u) (hu1 : u < 1) (hs : 0 ≤ s)
    (hD : D ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - lossFactor ((Real.pi * u) ^ 2 /
        (Real.pi ^ 2 - (Real.pi * u) ^ 2)) / 6 *
        ((3 / 2) * s) * (1 - ((Real.pi * u) / Real.pi) ^ 2 / 2))) :
    D ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - radialLower u * s * (1 - u ^ 2 / 2) / 4) := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have hid : (Real.pi * u) ^ 2 / (Real.pi ^ 2 - (Real.pi * u) ^ 2) =
      u ^ 2 / (1 - u ^ 2) := by
    field_simp [Real.pi_ne_zero, ne_of_gt hden]
  have htime : (Real.pi * u) / Real.pi = u := by
    field_simp [Real.pi_ne_zero]
  rw [hid, htime] at hD
  have hc := radialLower_le_lossFactor hu hu1
  have hw : 0 ≤ s * (1 - u ^ 2 / 2) := by
    apply mul_nonneg hs
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hc hw
  have hsin : 0 ≤ Real.sin (Real.pi * u) ^ 3 := by
    apply pow_nonneg
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hscaled := mul_le_mul_of_nonneg_left hmul hsin
  nlinarith only [hD, hscaled]

/-- The upper-volume estimate with the averaged radial determinant bound.
The only volume premise is the classical polar integration upper bound;
the sharp deficit coefficient is derived here. -/
theorem volume_ratio_upper_of_averaged_radial {D : ℝ → ℝ} {V s : ℝ}
    (hs : 0 ≤ s)
    (hD0 : IntervalIntegrable D volume 0 (5 / 8))
    (hD1 : IntervalIntegrable D volume (5 / 8) 1)
    (hpolar : V ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), D u) + ∫ u in (5 / 8 : ℝ)..1, D u))
    (hD : ∀ u, 0 < u → u < 1 → D u ≤ Real.sin (Real.pi * u) ^ 3 *
      (1 - lossFactor ((Real.pi * u) ^ 2 /
        (Real.pi ^ 2 - (Real.pi * u) ^ 2)) / 6 *
        ((3 / 2) * s) * (1 - ((Real.pi * u) / Real.pi) ^ 2 / 2))) :
    V ≤ 1 - (3 / 40) * s := by
  apply volume_ratio_upper_of_radial_comparison_open hs hD0 hD1 hpolar
  · intro u hu
    have h := averaged_radial_piecewise_bound hu.1.le (by linarith [hu.2]) hs
      (hD u hu.1 (by linarith [hu.2]))
    rw [radialLower, ite_eq_left hu.2.le] at h
    convert h using 1 ; unfold upperKernel ; field_simp [Real.pi_ne_zero] ; ring
  · intro u hu
    have h := averaged_radial_piecewise_bound (by linarith [hu.1]) hu.2 hs
      (hD u (by linarith [hu.1]) hu.2)
    rw [radialLower, ite_eq_right (not_le.mpr hu.1)] at h
    convert h using 1 ; unfold upperKernelEnd ; field_simp [Real.pi_ne_zero] ; ring

end

end PositiveEinsteinFour.Jacobi

end OAI
