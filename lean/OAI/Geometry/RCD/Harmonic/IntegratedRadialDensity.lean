import Mathlib

namespace OAI

/-! # Integrating the radial area-density comparison on positive intervals -/

open Set MeasureTheory

namespace RegularPointCoordinates

theorem integrated_radial_density_ratio {V w : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hw : Continuous w)
    (hV : AbsolutelyContinuousOnInterval V a c)
    (hcomp : ∀ x ∈ Icc a b, ∀ y ∈ Icc b c,
      DifferentiableAt ℝ V x → DifferentiableAt ℝ V y →
      w x * deriv V y ≤ w y * deriv V x) :
    (V c - V a) * (∫ s in a..b, w s) ≤
      (V b - V a) * (∫ s in a..c, w s) := by
  have hVac : ∀ᵐ x ∂volume, x ∈ Icc a c → DifferentiableAt ℝ V x := by
    simpa only [uIcc_of_le (hab.trans hbc)] using hV.ae_differentiableAt
  have hVab : AbsolutelyContinuousOnInterval V a b := hV.mono (by
    rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc_right hbc)
  have hVbc : AbsolutelyContinuousOnInterval V b c := hV.mono (by
    rw [uIcc_of_le hbc, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc_left hab)
  have hWab : IntervalIntegrable w volume a b := hw.intervalIntegrable a b
  have hWbc : IntervalIntegrable w volume b c := hw.intervalIntegrable b c
  have hfirst (y : ℝ) (hy : y ∈ Icc b c) (hdy : DifferentiableAt ℝ V y) :
      (∫ x in a..b, w x) * deriv V y ≤ w y * (V b - V a) := by
    have hp : (fun x => w x * deriv V y) ≤ᵐ[volume.restrict (Icc a b)]
        fun x => w y * deriv V x := by
      filter_upwards [ae_restrict_of_ae hVac, ae_restrict_mem measurableSet_Icc] with x hx hxab
      exact hcomp x hxab y hy (hx ⟨hxab.1, hxab.2.trans hbc⟩) hdy
    have hi := intervalIntegral.integral_mono_ae_restrict hab
      (hWab.mul_const (deriv V y)) (hVab.intervalIntegrable_deriv.const_mul (w y)) hp
    simpa only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      hVab.integral_deriv_eq_sub] using hi
  have hp : (fun y => (∫ x in a..b, w x) * deriv V y) ≤ᵐ[volume.restrict (Icc b c)]
      fun y => w y * (V b - V a) := by
    filter_upwards [ae_restrict_of_ae hVac, ae_restrict_mem measurableSet_Icc] with y hy hybc
    exact hfirst y hybc (hy ⟨hab.trans hybc.1, hybc.2⟩)
  have hi := intervalIntegral.integral_mono_ae_restrict hbc
    (hVbc.intervalIntegrable_deriv.const_mul (∫ x in a..b, w x))
    (hWbc.mul_const (V b - V a)) hp
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    hVbc.integral_deriv_eq_sub] at hi
  have hadd := intervalIntegral.integral_add_adjacent_intervals hWab hWbc
  rw [← hadd]
  nlinarith only [hi]

end RegularPointCoordinates

end OAI
