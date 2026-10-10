import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # The integrating factor estimate for a continuously forced energy -/

open Set MeasureTheory

namespace DefocusingNLS

theorem weighted_energy_estimate (F D H : ℝ → ℝ) (c t : ℝ) (ht : 0 ≤ t)
    (hF : Continuous F) (hD : Continuous D) (hH : Continuous H)
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt F (D s) s)
    (hbound : ∀ s ∈ Icc 0 t, D s ≤ -c * F s + H s) :
    Real.exp (c * t) * F t ≤ F 0 + ∫ s in (0 : ℝ)..t, Real.exp (c * s) * H s := by
  let G := fun s => Real.exp (c * s) * F s
  let Gd := fun s => Real.exp (c * s) * (c * F s + D s)
  have hG : Continuous G := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF
  have hGd : Continuous Gd :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul ((continuous_const.mul hF).add hD)
  have hGderiv (s : ℝ) (hs : s ∈ Ioo 0 t) : HasDerivAt G (Gd s) s := by
    have he := ((hasDerivAt_id s).const_mul c).exp.mul (hd s hs)
    convert he using 1
    · rfl
    · dsimp [Gd]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hG.continuousOn hGderiv
    (hGd.intervalIntegrable 0 t)
  have hmaj : Continuous (fun s => Real.exp (c * s) * H s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hH
  have hb : (∫ s in (0 : ℝ)..t, Gd s) ≤ ∫ s in (0 : ℝ)..t, Real.exp (c * s) * H s := by
    apply intervalIntegral.integral_mono_on ht (hGd.intervalIntegrable 0 t) (hmaj.intervalIntegrable 0 t)
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith [hbound s hs]
  dsimp only [G] at hi
  simp only [mul_zero, Real.exp_zero, one_mul] at hi
  linarith

theorem energy_decay_estimate (F D H : ℝ → ℝ) (c t : ℝ) (ht : 0 ≤ t)
    (hF : Continuous F) (hD : Continuous D) (hH : Continuous H)
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt F (D s) s)
    (hbound : ∀ s ∈ Icc 0 t, D s ≤ -c * F s + H s) :
    F t ≤ Real.exp (-c * t) * F 0 +
      ∫ s in (0 : ℝ)..t, Real.exp (-c * (t - s)) * H s := by
  have hw := mul_le_mul_of_nonneg_left
    (weighted_energy_estimate F D H c t ht hF hD hH hd hbound) (Real.exp_pos (-c * t)).le
  have hcancel : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
    rw [← Real.exp_add]
    have he : -c * t + c * t = 0 := by ring
    rw [he, Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul, mul_add, ← intervalIntegral.integral_const_mul] at hw
  convert hw using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end DefocusingNLS

end OAI
