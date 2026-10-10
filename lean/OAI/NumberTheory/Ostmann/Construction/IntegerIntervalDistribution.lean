import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionLiftCount

namespace OAI

/-! # Elementary interval distribution for the external integer giant -/

namespace Ostmann

open scoped Classical
open MeasureTheory

theorem integer_interval_residue_error (lo hi q a : ℕ) (hlo : lo ≤ hi) (hq : 0 < q) :
    |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ((hi : ℝ) - lo) / q| ≤ 1 := by
  let A : ℚ := ((lo : ℚ) - a) / q
  let B : ℚ := ((hi : ℚ) - a) / q
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (by exact_mod_cast hlo : (lo : ℚ) ≤ hi) a) hq'.le
  have hf := Int.floor_mono hAB
  have hcard := Nat.Ioc_filter_modEq_card lo hi hq a
  have hcast : (((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) =
      ((⌊B⌋ : ℤ) : ℚ) - ((⌊A⌋ : ℤ) : ℚ) := by
    rw [max_eq_left (sub_nonneg.mpr hf)] at hcard
    exact_mod_cast hcard
  have hA := Int.floor_le A
  have hA' := Int.lt_floor_add_one A
  have hB := Int.floor_le B
  have hB' := Int.lt_floor_add_one B
  have hrat : |(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| ≤ 1 := by
    rw [hcast]
    have hid : ((hi : ℚ) - lo) / q = B - A := by dsimp [A, B]; ring
    rw [hid, abs_le]
    constructor <;> linarith
  have hr : ((|(((Finset.Ioc lo hi).filter fun n => Nat.ModEq q n a).card : ℚ) -
      ((hi : ℚ) - lo) / q| : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hrat
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using hr

theorem real_interval_residue_error (q a : ℕ) (hq : 0 < q) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) :
    |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) -
      (v - u) / q| ≤ 2 := by
  have h := integer_interval_residue_error ⌊u⌋₊ ⌊v⌋₊ q a (Nat.floor_mono huv) hq
  have hv : 0 ≤ v := hu.trans huv
  have hu0 := Nat.floor_le hu
  have hu1 := Nat.lt_floor_add_one u
  have hv0 := Nat.floor_le hv
  have hv1 := Nat.lt_floor_add_one v
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : |(((⌊v⌋₊ : ℕ) : ℝ) - ⌊u⌋₊) / q - (v - u) / q| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hq0, div_le_one hq0, abs_le]
    constructor <;> linarith
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ)
    ((((⌊v⌋₊ : ℕ) : ℝ) - ⌊u⌋₊) / q) ((v - u) / q)
  simp only [Real.norm_eq_abs] at ht
  linarith

/-- The logarithmic integer coordinate has main density `exp(t)/q`.
Multiplication by its original normalization costs exactly the same factor
on the uniform absolute error. -/
theorem integer_log_interval_residue_error (q a : ℕ) (hq : 0 < q)
    (s t G : ℝ) (hst : s ≤ t) :
    |Real.exp (-G) *
      (((Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) -
      Real.exp (-G) * ((Real.exp t - Real.exp s) / q)| ≤ 2 * Real.exp (-G) := by
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left
    (real_interval_residue_error q a hq (Real.exp_pos s).le (Real.exp_le_exp.mpr hst))
    (Real.exp_pos (-G)).le).trans_eq (mul_comm _ _)

noncomputable def integerLogDensity (q : ℕ) (G y : ℝ) : ℝ :=
  Real.exp (y - G) / q

theorem integerLogDensity_integral (q : ℕ) (s t G : ℝ) (hst : s ≤ t) :
    (∫ y in Set.Ioc s t, integerLogDensity q G y) =
      Real.exp (-G) * ((Real.exp t - Real.exp s) / q) := by
  calc
    _ = ∫ y in Set.Ioc s t, (Real.exp (-G) / q) * Real.exp y := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y _
      dsimp [integerLogDensity]
      rw [Real.exp_sub, Real.exp_neg]
      ring
    _ = (Real.exp (-G) / q) * (∫ y in Set.Ioc s t, Real.exp y) := integral_const_mul _ _
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hst, integral_exp]
      ring

/-- The external integer coordinate has the claimed real log density,
with an explicit absolute error uniform in every residue class. -/
theorem integer_log_density_error (q a : ℕ) (hq : 0 < q)
    (s t G : ℝ) (hst : s ≤ t) :
    |Real.exp (-G) *
      (((Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter fun n => Nat.ModEq q n a).card : ℝ) -
      ∫ y in Set.Ioc s t, integerLogDensity q G y| ≤ 2 * Real.exp (-G) := by
  rw [integerLogDensity_integral q s t G hst]
  exact integer_log_interval_residue_error q a hq s t G hst

end Ostmann

end OAI
