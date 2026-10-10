import Mathlib.Data.Nat.Choose.Sum

namespace OAI

namespace PeriodicTilingThree

open scoped BigOperators

private theorem binomial_two_terms_le (a m : ℕ) (hm : 2 ≤ m) :
    a ^ m + a ^ (m - 2) * m.choose 2 ≤ (1 + a) ^ m := by
  have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range (m + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simp only [Finset.mem_range]
      omega
    · simp only [Finset.mem_range]
      omega
  calc
    a ^ m + a ^ (m - 2) * m.choose 2 =
        ∑ k ∈ ({0, 2} : Finset ℕ), 1 ^ k * a ^ (m - k) * m.choose k := by
      simp
    _ ≤ ∑ k ∈ Finset.range (m + 1), 1 ^ k * a ^ (m - k) * m.choose k :=
      Finset.sum_le_sum_of_subset hsub
    _ = (1 + a) ^ m := (add_pow 1 a m).symm

theorem fullDifference_bad_bound (s m : ℕ) (hs : 2 ≤ s)
    (hm : 4 * s * (s ^ 2 - 1) ^ 2 + 1 ≤ m) :
    s * (2 * m) * (s ^ 2 - 1) ^ m < s ^ (2 * m) := by
  let a : ℕ := s ^ 2 - 1
  have hsquare : 4 ≤ s ^ 2 := by
    simpa using Nat.pow_le_pow_left hs 2
  have ha : 0 < a := by
    dsimp [a]
    omega
  have ha_succ : 1 + a = s ^ 2 := by
    dsimp [a]
    omega
  change 4 * s * a ^ 2 + 1 ≤ m at hm
  have hthreshold : 0 < 4 * s * a ^ 2 :=
    Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (pow_pos ha 2)
  have hm_two : 2 ≤ m := by omega
  have hpred : 4 * s * a ^ 2 ≤ m - 1 := by omega
  have hchoose : m.choose 2 * 2 = m * (m - 1) := by
    simpa using Nat.choose_succ_right_eq m 1
  have hdoubled : (2 * s * m * a ^ 2) * 2 ≤ m.choose 2 * 2 := by
    calc
      (2 * s * m * a ^ 2) * 2 = m * (4 * s * a ^ 2) := by ring
      _ ≤ m * (m - 1) := Nat.mul_le_mul_left m hpred
      _ = m.choose 2 * 2 := hchoose.symm
  have hcoefficient : 2 * s * m * a ^ 2 ≤ m.choose 2 := by
    omega
  have hpower : a ^ 2 * a ^ (m - 2) = a ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' hm_two]
  have hterm : (2 * s * m) * a ^ m ≤ a ^ (m - 2) * m.choose 2 := by
    calc
      (2 * s * m) * a ^ m = a ^ (m - 2) * (2 * s * m * a ^ 2) := by
        rw [← hpower]
        ring
      _ ≤ a ^ (m - 2) * m.choose 2 :=
        Nat.mul_le_mul_left (a ^ (m - 2)) hcoefficient
  have hpositive : 0 < a ^ m := pow_pos ha m
  calc
    s * (2 * m) * (s ^ 2 - 1) ^ m = (2 * s * m) * a ^ m := by
      dsimp [a]
      ring
    _ < a ^ m + a ^ (m - 2) * m.choose 2 := by omega
    _ ≤ (1 + a) ^ m := binomial_two_terms_le a m hm_two
    _ = s ^ (2 * m) := by rw [ha_succ, ← pow_mul]

theorem fullDifference_bad_bound_poly (s m : ℕ) (hs : 2 ≤ s)
    (hm : 4 * s ^ 5 + 1 ≤ m) :
    s * (2 * m) * (s ^ 2 - 1) ^ m < s ^ (2 * m) := by
  apply fullDifference_bad_bound s m hs
  calc
    4 * s * (s ^ 2 - 1) ^ 2 + 1 ≤ 4 * s * (s ^ 2) ^ 2 + 1 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left (4 * s) (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)) 1
    _ = 4 * s ^ 5 + 1 := by ring
    _ ≤ m := hm

end PeriodicTilingThree

end OAI
