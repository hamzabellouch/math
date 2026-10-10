import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates
import OAI.NumberTheory.Ostmann.Characters.CharacterFourierBudgets

namespace OAI

/-! # Integer endpoints for the separated character prime bands -/
namespace Ostmann
open Filter

/-- A fixed positive gap in log-log scale supplies the factor two required
by the one-sided character estimate, even after rounding upward. -/
theorem eventual_double_exp_integer_margin (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      2 * (⌈Real.exp (Real.exp (α * L))⌉₊ : ℝ) ≤ Real.exp (Real.exp (β * L)) := by
  filter_upwards [arithmetic_exponent_absorption α β 0 4 1 0 hβ hαβ hβ (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hgap hL
  simp only [pow_zero, zero_mul, Real.exp_zero, one_mul] at hgap
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hm := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg (α * L))
  have he : Real.log 4 + Real.exp (α * L) ≤ Real.exp (β * L) := by
    nlinarith only [hgap, hm, Real.exp_nonneg (α * L), hlog4]
  have hceil := (Nat.ceil_lt_add_one (Real.exp_nonneg (Real.exp (α * L)))).le
  have hexp : 1 ≤ Real.exp (Real.exp (α * L)) :=
    Real.one_le_exp (Real.exp_nonneg _)
  calc
    _ ≤ 4 * Real.exp (Real.exp (α * L)) := by linarith
    _ = Real.exp (Real.log 4 + Real.exp (α * L)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem eventual_character_band_lower (α β : ℝ) (hβ : 0 < β) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop,
      let A := ⌈Real.exp (Real.exp (α * L))⌉₊
      0 < A ∧ Real.exp (Real.exp (α * L)) ≤ A ∧
        ∀ p : ℕ, Real.exp (Real.exp (β * L)) ≤ p → 2 * A ≤ p := by
  filter_upwards [eventual_double_exp_integer_margin α β hβ hαβ] with L hL
  refine ⟨Nat.ceil_pos.mpr (Real.exp_pos _), Nat.le_ceil _, ?_⟩
  intro p hp
  exact_mod_cast hL.trans hp

theorem character_band_upper (β L : ℝ) (p : ℕ)
    (hp : (p : ℝ) ≤ Real.exp (Real.exp (β * L))) :
    p ≤ ⌊Real.exp (Real.exp (β * L))⌋₊ ∧
      (⌊Real.exp (Real.exp (β * L))⌋₊ : ℝ) ≤ Real.exp (Real.exp (β * L)) :=
  ⟨Nat.le_floor hp, Nat.floor_le (Real.exp_nonneg _)⟩

end Ostmann

end OAI
