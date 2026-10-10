import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped BigOperators

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

def scalarCollisionCount (E : Finset F) (a : F) : ℕ :=
  (((E.product E).product (E.product E)).filter
    (fun p => p.1.1 + a * p.1.2 = p.2.1 + a * p.2.2)).card

theorem scalarCollisionCount_eq_sum (E : Finset F) (a : F) :
    scalarCollisionCount E a =
      ∑ x ∈ E, ∑ y ∈ E, ∑ x' ∈ E, ∑ y' ∈ E,
        if x + a * y = x' + a * y' then 1 else 0 := by
  simp only [scalarCollisionCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, Finset.sum_product]

theorem scalarCollision_iff_eq_div (x y x' y' : F) (hy : y ≠ y') (a : F) :
    x + a * y = x' + a * y' ↔ a = (x' - x) / (y - y') := let _ := instDecidableEqF; by
  have hlinear : x + a * y = x' + a * y' ↔ a * (y - y') = x' - x := by
    constructor
    · intro h
      calc
        a * (y - y') = (x + a * y) - (x' + a * y') + (x' - x) := by ring
        _ = x' - x := by rw [h]; ring
    · intro h
      calc
        x + a * y = (a * (y - y') - (x' - x)) + (x' + a * y') := by ring
        _ = x' + a * y' := by rw [h]; ring
  exact hlinear.trans (eq_div_iff (sub_ne_zero.mpr hy)).symm

variable [Fintype F]

private theorem sum_scalarCollision_indicator (x y x' y' : F) :
    (∑ a : F, if x + a * y = x' + a * y' then (1 : ℕ) else 0) +
        (if y = y' then 1 else 0) =
      (if x = x' ∧ y = y' then Fintype.card F else 0) + 1 := by
  by_cases hy : y = y'
  · subst y'
    by_cases hx : x = x'
    · subst x'
      simp
    · simp [hx]
  · simp_rw [scalarCollision_iff_eq_div x y x' y' hy]
    simp [hy]

theorem sum_scalarCollisionCount (E : Finset F) :
    (∑ a : F, scalarCollisionCount E a) + E.card ^ 3 =
      Fintype.card F * E.card ^ 2 + E.card ^ 4 := by
  let Q := (E.product E).product (E.product E)
  have hcount :
      (∑ a : F, scalarCollisionCount E a) =
        ∑ p ∈ Q, ∑ a : F,
          if p.1.1 + a * p.1.2 = p.2.1 + a * p.2.2 then (1 : ℕ) else 0 := by
    simp only [scalarCollisionCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsecond :
      (∑ p ∈ Q, if p.1.2 = p.2.2 then (1 : ℕ) else 0) = E.card ^ 3 := by
    dsimp [Q]
    simp only [Finset.sum_product]
    calc
      (∑ x ∈ E, ∑ y ∈ E, ∑ x' ∈ E, ∑ y' ∈ E,
          if y = y' then (1 : ℕ) else 0) = ∑ x ∈ E, ∑ y ∈ E, E.card := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        simp [hy]
      _ = E.card ^ 3 := by simp; ring
  have hdiagonal :
      (∑ p ∈ Q, if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2
        then Fintype.card F else 0) = Fintype.card F * E.card ^ 2 := by
    dsimp [Q]
    simp only [Finset.sum_product]
    calc
      (∑ x ∈ E, ∑ y ∈ E, ∑ x' ∈ E, ∑ y' ∈ E,
          if x = x' ∧ y = y' then Fintype.card F else 0) =
          ∑ x ∈ E, ∑ y ∈ E, Fintype.card F := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        calc
          (∑ x' ∈ E, ∑ y' ∈ E,
              if x = x' ∧ y = y' then Fintype.card F else 0) =
              ∑ x' ∈ E, if x = x' then Fintype.card F else 0 := by
            apply Finset.sum_congr rfl
            intro x' hx'
            by_cases hxx : x = x'
            · simp [hxx, hy]
            · simp [hxx]
          _ = Fintype.card F := by simp [hx]
      _ = Fintype.card F * E.card ^ 2 := by simp; ring
  have hquadruples : (∑ p ∈ Q, (1 : ℕ)) = E.card ^ 4 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    dsimp [Q]
    rw [Finset.card_product, Finset.card_product]
    ring
  have hsum :
      (∑ p ∈ Q,
        ((∑ a : F, if p.1.1 + a * p.1.2 = p.2.1 + a * p.2.2
          then (1 : ℕ) else 0) + (if p.1.2 = p.2.2 then 1 else 0))) =
      ∑ p ∈ Q,
        ((if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then Fintype.card F else 0) + 1) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact sum_scalarCollision_indicator p.1.1 p.1.2 p.2.1 p.2.2
  simp only [Finset.sum_add_distrib] at hsum
  rw [← hcount, hsecond, hdiagonal, hquadruples] at hsum
  exact hsum

end RyserCoveringCounterexample.Incidence

end OAI
