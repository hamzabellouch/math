import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeLogDensity
import OAI.NumberTheory.Ostmann.ZeroDensity.PageFactors

namespace OAI

/-! # Bounds on the retained density and on discarded real zeros -/

namespace Ostmann

open MeasureTheory

theorem continuousOn_primeLogDensity (φ χ β : ℝ) {s t : ℝ} (hs : 0 < s) :
    ContinuousOn (primeLogDensity φ χ β) (Set.Icc s t) := by
  intro y hy
  have hy0 : y ≠ 0 := ne_of_gt (hs.trans_le hy.1)
  have hn : ContinuousAt (fun y : ℝ =>
      (1 - χ * Real.exp ((β - 1) * y)) / y) y :=
    (continuousAt_const.sub ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).const_mul χ)).div continuousAt_id hy0
  apply ((hn.div_const φ).congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [] with x
  dsimp [primeLogDensity]
  ring

theorem primeLogDensity_bounds (φ χ β : ℝ) (hφ : 0 ≤ φ)
    (hχ : |χ| ≤ 1) (hβ : β ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ primeLogDensity φ χ β t ∧ primeLogDensity φ χ β t ≤ 2 / (φ * t) := by
  have h := pageMultiplier_bounds (fun _ : Unit => χ) β t (fun _ => hχ) hβ ht ()
  dsimp [pageMultiplier] at h
  exact ⟨div_nonneg h.1 (mul_nonneg hφ ht),
    div_le_div_of_nonneg_right h.2 (mul_nonneg hφ ht)⟩

/-- A zero separated from one by `d` contributes at most `exp (-d*s)`
throughout a logarithmic interval beginning at `s ≥ 1`. -/
theorem primeLogDensity_correction_le (φ χ β d : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hd : 0 ≤ d) (hβ : β ≤ 1 - d)
    {s y : ℝ} (hs : 1 ≤ s) (hsy : s ≤ y) :
    |primeLogDensity φ χ β y - primeLogDensity φ 0 1 y| ≤
      Real.exp (-d * s) := by
  have hy : (1 : ℝ) ≤ y := hs.trans hsy
  have hden : (1 : ℝ) ≤ φ * y := by nlinarith
  have hden0 : 0 < φ * y := lt_of_lt_of_le zero_lt_one hden
  have hid : primeLogDensity φ χ β y - primeLogDensity φ 0 1 y =
      -(χ * Real.exp ((β - 1) * y)) / (φ * y) := by
    dsimp [primeLogDensity]
    ring
  rw [hid, abs_div, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hden0]
  have hexp : Real.exp ((β - 1) * y) ≤ Real.exp (-d * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp ((β - 1) * y) / (φ * y) :=
      div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hχ (Real.exp_pos _).le) hden0.le
    _ ≤ Real.exp (-d * s) / (φ * y) := div_le_div_of_nonneg_right hexp hden0.le
    _ ≤ Real.exp (-d * s) := (div_le_self (Real.exp_pos _).le hden)

theorem primeLogDensity_integral_correction_le (φ χ β d : ℝ) (hφ : 1 ≤ φ)
    (hχ : |χ| ≤ 1) (hd : 0 ≤ d) (hβ : β ≤ 1 - d)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |(∫ y in Set.Ioc s t, primeLogDensity φ χ β y) -
      (∫ y in Set.Ioc s t, primeLogDensity φ 0 1 y)| ≤ Real.exp (-d * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hI (χ β : ℝ) : IntegrableOn (primeLogDensity φ χ β) (Set.Ioc s t) :=
    (continuousOn_primeLogDensity φ χ β hs0).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [← integral_sub (hI χ β) (hI 0 1)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (C := Real.exp (-d * s))
    (f := fun y => primeLogDensity φ χ β y - primeLogDensity φ 0 1 y)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      exact primeLogDensity_correction_le φ χ β d hφ hχ hd hβ hs
        (((Set.uIoc_of_le hst) ▸ hy).1.le))
  rw [intervalIntegral.integral_of_le hst, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hst)] at hi
  exact hi.trans (by nlinarith [Real.exp_pos (-d * s)])

end Ostmann

end OAI
