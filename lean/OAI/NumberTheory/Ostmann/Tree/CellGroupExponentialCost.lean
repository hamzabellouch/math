import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Tree.CellGroupPigeonhole

namespace OAI

/-! # The exact cell-list pigeonhole costs only a fixed exponential in m -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_cell_group_cost (N r : ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 1 ≤ z) (hsize : (N + r : ℕ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m →
      (((N + r + 1) * (max N B + 1) ^ (N + r) : ℕ) : ℝ) ≤
        Real.exp (2 * (C + 2) * m) := by
  filter_upwards [eventually_ge_atTop (max 0 (max (Real.log (N + r + 1 : ℕ))
    (Real.log (N + 1 : ℕ))))] with L hL
  intro B m hB hm
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hLr : Real.log (N + r + 1 : ℕ) ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLN : Real.log (N + 1 : ℕ) ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hpref : (N + r + 1 : ℕ) ≤ Real.exp L := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (N + r + 1 : ℕ))]
    exact Real.exp_le_exp.mpr hLr
  have hN : (N + 1 : ℕ) ≤ Real.exp L := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (N + 1 : ℕ))]
    exact Real.exp_le_exp.mpr hLN
  have hmax : (max N B + 1 : ℕ) ≤ Real.exp ((C + 1) * L) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_max, ← max_add_add_right]
    apply max_le
    · exact (show (N : ℝ) + 1 ≤ Real.exp L from by simpa only [Nat.cast_add, Nat.cast_one] using hN).trans
        (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hC hL0]))
    · exact (show (B : ℝ) + 1 ≤ Real.exp (C * L) from by simpa only [Nat.cast_add, Nat.cast_one] using hB).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hL0]))
  calc
    _ ≤ Real.exp L * (Real.exp ((C + 1) * L)) ^ (N + r) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      exact mul_le_mul hpref (pow_le_pow_left₀ (Nat.cast_nonneg _) hmax _)
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((1 + (C + 1) * (N + r : ℕ)) * L) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((C + 2) * z * L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsize (by linarith : 0 ≤ C + 1)
      have hcoef : 1 + (C + 1) * (N + r : ℕ) ≤ (C + 2) * z := by nlinarith only [hh, hz]
      exact mul_le_mul_of_nonneg_right hcoef hL0
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ C + 2)
      nlinarith only [hh])

/-- The endpoint count after fixing all cell lists keeps an explicit
exponential rate, with no dependence on the number of fixed labels in it. -/
theorem cell_group_endpoint_rate (e s : ℕ) (F X A B m : ℝ)
    (hcount : (e : ℝ) ≤ F * s) (hF : F ≤ Real.exp (B * m))
    (he : Real.sqrt X * Real.exp (-A * m) ≤ e) :
    Real.sqrt X * Real.exp (-(A + B) * m) ≤ s := by
  have hb : Real.sqrt X * Real.exp (-A * m) ≤ Real.exp (B * m) * s :=
    he.trans (hcount.trans (mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg s)))
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-B * m))
  have hid : Real.exp (-B * m) * (Real.exp (B * m) * (s : ℝ)) = s := by
    rw [← mul_assoc, ← Real.exp_add, show -B * m + B * m = 0 by ring, Real.exp_zero, one_mul]
  rw [hid] at hh
  calc
    _ = Real.exp (-B * m) * (Real.sqrt X * Real.exp (-A * m)) := by
      calc
        _ = Real.sqrt X * (Real.exp (-B * m) * Real.exp (-A * m)) := by
          rw [← Real.exp_add]
          congr 1
          congr 1
          ring
        _ = _ := by ring
    _ ≤ _ := hh

end Ostmann

end OAI
