import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import OAI.Computability.UniqueGames.Inverse.RowErasureLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

theorem table_expect_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) :
    Finset.univ.expect (fun r : X → Y => ∏ x, f x (r x)) =
      ∏ x, Finset.univ.expect (f x) := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow]

private theorem exp_half_le_seven_quarters : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem exp_half_indicator (P : Prop) :
    Real.exp (indicator P / 2) = 1 + (Real.exp (1 / 2 : ℝ) - 1) * indicator P := by
  classical
  by_cases h : P <;> simp [indicator, h]

theorem table_coordinate_exp_le {Y : Type*} [Fintype Y] [Nonempty Y]
    (P : Prop) (target : Y) :
    Finset.univ.expect (fun y => Real.exp (indicator (P ∧ y = target) / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hP : P
  · have hsingle : Finset.univ.expect (fun y : Y => indicator (y = target)) =
        1 / (Fintype.card Y : ℝ) := by
      simp [indicator]
    have heq : Finset.univ.expect
        (fun y => Real.exp (indicator (P ∧ y = target) / 2)) =
        1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) := by
      simp_rw [hP, true_and, exp_half_indicator]
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, hsingle]
      simp [div_eq_mul_inv]
    rw [heq]
    calc
      1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) ≤
          1 + 3 / (4 * (Fintype.card Y : ℝ)) := by
        have h := div_le_div_of_nonneg_right
          (show Real.exp (1 / 2 : ℝ) - 1 ≤ 3 / 4 by
            linarith [exp_half_le_seven_quarters]) hcard.le
        simpa only [div_div, add_comm] using add_le_add_left h 1
      _ ≤ Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
        simpa only [add_comm] using Real.add_one_le_exp (3 / (4 * (Fintype.card Y : ℝ)))
  · simp only [hP, false_and, indicator_false, zero_div, Real.exp_zero,
      Fintype.expect_const]
    exact Real.one_le_exp (by positivity)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
