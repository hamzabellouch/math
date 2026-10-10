import Mathlib

namespace OAI

namespace Problem346

open scoped BigOperators

/-- The parameter reduction in the induction on the outer symmetric degree. -/
theorem stabilization_reduction {a b : ℕ} (ha : 2 ≤ a)
    (hab : a * (a - 1) ≤ b) :
    let r := a - 1
    let m := b - r
    1 ≤ r ∧ r * (r + 1) ≤ b ∧ r * r ≤ m ∧
      1 ≤ m ∧ r * (r - 1) ≤ m := by
  dsimp
  have ha' : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  have hr : 1 ≤ a - 1 := by omega
  have hb : (a - 1) * ((a - 1) + 1) ≤ b := by
    rw [ha', Nat.mul_comm]
    exact hab
  have hm : (a - 1) * (a - 1) ≤ b - (a - 1) := by
    apply Nat.le_sub_of_add_le
    nlinarith
  have hmpos : 1 ≤ b - (a - 1) := by nlinarith
  refine ⟨hr, hb, hm, hmpos, ?_⟩
  exact (Nat.mul_le_mul_left (a - 1) (Nat.sub_le (a - 1) 1)).trans hm

/-- The first sequence of shifts has positive source-minus-destination weight. -/
theorem first_shift_weight {b r i : ℕ} (hir : i ≤ b - r)
    (hi : 1 ≤ i) : r < b - i + 1 := by
  omega

/-- The shared destination variable remains at least two degrees below the source. -/
theorem second_shift_weight_gap {b r i j : ℕ}
    (hr : 1 ≤ r) (hb : r * (r + 1) ≤ b)
    (hi : 1 ≤ i) (hir : i ≤ r) (hj : j < r) :
    (i - 1) * r + j + 2 ≤ b - j := by
  have hi' : i - 1 ≤ r - 1 := by omega
  have hmul : (i - 1) * r ≤ (r - 1) * r := Nat.mul_le_mul_right r hi'
  have hr' : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hj' : j ≤ r - 1 := by omega
  have hbound : (i - 1) * r + j + 2 + j ≤ b := by nlinarith
  exact Nat.le_sub_of_add_le hbound

/-- The second sequence of shifts satisfies the strict injectivity inequality. -/
theorem second_shift_weight {b r i j : ℕ}
    (hr : 1 ≤ r) (hb : r * (r + 1) ≤ b)
    (hi : 1 ≤ i) (hir : i ≤ r) (hj : j < r) :
    (i - 1) * r + j < b - j := by
  have h := second_shift_weight_gap hr hb hi hir hj
  omega

/-- Arbitrary progress vectors, rather than only lexicographic schedules, satisfy the
positive-weight inequality at every unfinished slot. -/
theorem grid_shift_weight {b r : ℕ} (hb : r * (r + 1) ≤ b)
    (counts : Fin r → ℕ) (hcounts : ∀ j, counts j ≤ r)
    (i : Fin r) (hi : counts i < r) :
    (∑ j, counts j) < b - counts i := by
  have hsum : (∑ j, counts j) ≤ r * r := by
    calc
      (∑ j, counts j) ≤ ∑ _j : Fin r, r :=
        Finset.sum_le_sum (fun j _ => hcounts j)
      _ = r * r := by simp
  have hbound : (∑ j, counts j) + counts i < b := by nlinarith
  omega

end Problem346

end OAI
