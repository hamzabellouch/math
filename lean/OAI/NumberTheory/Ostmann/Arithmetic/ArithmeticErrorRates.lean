import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

theorem arithmetic_error_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ n + C * L * Real.exp (a * L)) *
        Real.exp (-c * Real.exp (b * L)) ≤ Real.exp (-Real.exp (d * L)) := by
  filter_upwards [arithmetic_exponent_absorption a b d C c n hb hab hdb hc] with L hL
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The mesh variation error in the bulk idealization, including the
spectator and polynomial history costs. -/
theorem bulk_variation_error (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        Real.exp (-Real.exp ((14 / 10000 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  simpa only [one_mul, neg_mul] using
    arithmetic_error_absorption (1 / 1000) (14 / 10000) (125 / 100000) C 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The polynomial-root loss remains negligible after the same costs. -/
theorem symbolic_root_error (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        Real.exp (-c * Real.exp ((4 / 1000 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) :=
  arithmetic_error_absorption (1 / 1000) (4 / 1000) (2 / 1000) C c 2
    (by norm_num) (by norm_num) (by norm_num) hc

/-- The error from the bulk progression formula after counting joint boxes. -/
theorem bulk_progression_error (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (-c * Real.exp ((16 / 10000 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) :=
  arithmetic_error_absorption (14 / 10000) (16 / 10000) (125 / 100000) C c 2
    (by norm_num) (by norm_num) (by norm_num) hc

/-- Both the prime-square exclusions and the nonzero-polynomial prime-divisor
loss have the stronger internal-prime saving. -/
theorem internal_prime_error (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        Real.exp (-c * Real.exp ((1 / 100 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) :=
  arithmetic_error_absorption (1 / 1000) (1 / 100) (2 / 1000) C c 2
    (by norm_num) (by norm_num) (by norm_num) hc

/-- Freezing the two giant log coordinates has ample reserve. -/
theorem giant_variation_error (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        Real.exp (-Real.exp ((15 / 1000 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
  simpa only [one_mul, neg_mul] using
    arithmetic_error_absorption (12 / 1000) (15 / 1000) (13 / 1000) C 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Summing the giant progression errors over all boxes and residues. -/
theorem giant_progression_error (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((15 / 1000 : ℝ) * L)) *
        Real.exp (-c * Real.exp ((18 / 1000 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) :=
  arithmetic_error_absorption (15 / 1000) (18 / 1000) (13 / 1000) C c 2
    (by norm_num) (by norm_num) (by norm_num) hc

/-- The elementary external-integer error has a stronger saving. -/
theorem giant_integer_error (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C * L ^ 2 + C * L * Real.exp ((15 / 1000 : ℝ) * L)) *
        Real.exp (-c * Real.exp ((49 / 1000 : ℝ) * L)) ≤
          Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) :=
  arithmetic_error_absorption (15 / 1000) (49 / 1000) (13 / 1000) C c 2
    (by norm_num) (by norm_num) (by norm_num) hc

end Ostmann

end OAI
