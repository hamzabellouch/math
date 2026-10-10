import OAI.Combinatorics.Ryser.Incidence.FiniteSetCovering
import OAI.Combinatorics.Ryser.Incidence.FiniteSetEstimates
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.Lemmas

namespace OAI

open scoped Pointwise

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

theorem card_sub_swap (X Y : Finset F) : (X - Y).card = (Y - X).card := by
  calc
    (X - Y).card = (-(X - Y)).card := (Finset.card_neg _).symm
    _ = (Y - X).card := by rw [neg_sub]

theorem triangle_card_le (X Y Z : Finset F) :
    (X - Y).card * Z.card ≤ (X - Z).card * (Z - Y).card := by
  simpa only [card_sub_swap Y Z] using
    FiniteSetEstimates.ruzsa_triangle_inequality_sub_sub_sub X Z Y

theorem covering_sub (X Y : Finset F) (hY : Y.Nonempty) {M : ℝ}
    (hM : ((X - Y).card : ℝ) ≤ M * Y.card) :
    ∃ T ⊆ X, (T.card : ℝ) ≤ M ∧ X ⊆ T + (Y - Y) := by
  obtain ⟨T, hTX, hT, hcover⟩ :=
    FiniteSetEstimates.covering_add X (-Y) hY.neg
      (by simpa only [Finset.card_neg, sub_eq_add_neg] using hM)
  exact ⟨T, hTX, hT, by simpa only [neg_sub_neg] using hcover⟩

theorem multiple_sum_sub_card_le (Y : Finset F) (hY : Y.Nonempty) {M : ℝ}
    (hM : ((Y - Y).card : ℝ) ≤ M * Y.card) (u v : ℕ) :
    ((u • Y - v • Y).card : ℝ) ≤ M ^ (u + v) * Y.card := by
  have hNN := FiniteSetEstimates.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub
    (A := Y) hY Y u v
  have hRat : ((u • Y - v • Y).card : ℚ) ≤
      (((Y - Y).card : ℚ) / Y.card) ^ (u + v) * Y.card := by
    exact_mod_cast hNN
  have hReal : ((u • Y - v • Y).card : ℝ) ≤
      (((Y - Y).card : ℝ) / Y.card) ^ (u + v) * Y.card := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hRat
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hcast
  have hy : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hr : ((Y - Y).card : ℝ) / Y.card ≤ M := (div_le_iff₀ hy).2 hM
  exact hReal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hy.le) hr (u + v))
    (Nat.cast_nonneg _))

end RyserCoveringCounterexample.Incidence

end OAI
