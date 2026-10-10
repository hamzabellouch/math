import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialHardyInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # Small-ball energy estimates for bounded regular radial channels -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousRegular_poincare (R : ℝ) (hR : 0 ≤ R)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (huR : u R = 0) :
    16 * (∫ r in (0 : ℝ)..R, r ^ 11 * (u r) ^ 2) ≤
      R ^ 2 * (∫ r in (0 : ℝ)..R, r ^ 11 * (deriv u r) ^ 2) := by
  have hH := radialHardyInequality 0 R le_rfl (by norm_num) hR u hu huR
  simp only [radialHardyWeight, mul_zero, Real.rpow_zero, mul_one] at hH
  have hI : (∫ r in (0 : ℝ)..R, r ^ 11 * (u r) ^ 2) ≤
      R ^ 2 * (∫ r in (0 : ℝ)..R, r ^ 9 * (u r) ^ 2) := by
    have hA : Continuous (fun r : ℝ => r ^ 11 * (u r) ^ 2) := by fun_prop
    have hB : Continuous (fun r : ℝ => R ^ 2 * (r ^ 9 * (u r) ^ 2)) := by fun_prop
    have h := intervalIntegral.integral_mono_on hR
      (hA.intervalIntegrable (μ := volume) 0 R)
      (hB.intervalIntegrable (μ := volume) 0 R) (fun r hr => by
        have hrR : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
        have hp := mul_le_mul_of_nonneg_right hrR (mul_nonneg (pow_nonneg hr.1 9) (sq_nonneg (u r)))
        convert hp using 1
        ring)
    simpa only [intervalIntegral.integral_const_mul] using h
  nlinarith [mul_le_mul_of_nonneg_left hH (sq_nonneg R)]

theorem homogeneousRegular_energy_identity (R eta : ℝ) (hR : 0 ≤ R)
    (u H : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hH : Continuous H) (huR : u R = 0)
    (hODE : ∀ r, 0 < r → r ≤ R →
      deriv (deriv u) r + 11 / r * deriv u r - eta / r ^ 2 * u r = H r) :
    (∫ r in (0 : ℝ)..R, r ^ 11 * (deriv u r) ^ 2) +
      eta * (∫ r in (0 : ℝ)..R, r ^ 9 * (u r) ^ 2) =
        -(∫ r in (0 : ℝ)..R, r ^ 11 * u r * H r) := by
  let J := fun r => r ^ 11 * u r * deriv u r
  let A := fun r => r ^ 11 * (deriv u r) ^ 2 + eta * (r ^ 9 * (u r) ^ 2) +
    r ^ 11 * u r * H r
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hA : Continuous A := by
    dsimp only [A]
    fun_prop
  have hJ (r : ℝ) (hr : r ∈ Icc 0 R) : HasDerivAt J (A r) r := by
    have h := (((hasDerivAt_id r).pow 11).mul
      (hu.differentiable (by norm_num) r).hasDerivAt).mul
      (hud.differentiable (by norm_num) r).hasDerivAt
    apply h.congr_deriv
    rcases hr.1.eq_or_lt with hr0 | hr0
    · subst r
      simp [A]
    · have he := hODE r hr0 hr.2
      dsimp only [A]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, Pi.mul_apply, Pi.pow_apply, id_eq, mul_one]
      field_simp [hr0.ne'] at he
      linear_combination (r ^ 9 * u r) * he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hJ r (by simpa only [uIcc_of_le hR] using hr))
    (hA.intervalIntegrable (μ := volume) 0 R)
  have hi1 : IntervalIntegrable (fun r => r ^ 11 * (deriv u r) ^ 2) volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi2 : IntervalIntegrable (fun r => r ^ 9 * (u r) ^ 2) volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi3 : IntervalIntegrable (fun r => r ^ 11 * u r * H r) volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp only [J, huR, mul_zero, zero_pow (by norm_num : (11 : ℕ) ≠ 0), zero_mul, sub_self] at he
  dsimp only [A] at he
  rw [intervalIntegral.integral_add (hi1.add (hi2.const_mul eta)) hi3,
    intervalIntegral.integral_add hi1 (hi2.const_mul eta),
    intervalIntegral.integral_const_mul] at he
  linarith

end DefocusingNLS

end OAI
