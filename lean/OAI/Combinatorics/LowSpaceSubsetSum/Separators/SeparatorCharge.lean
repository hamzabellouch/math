import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorBlocks

namespace OAI

/-! # Polynomial charge bound for the composed separator traversal -/

namespace LowSpaceSubsetSum.SeparatorBlocks

open SeparatorIncidenceTable

variable {α β : Type*}

def coefficient (n : ℕ) (bs : List (Block α β)) : ℕ :=
  6 * n + 8 + 2 * (bs.map depth).sum

def multiplicityLeft (bs : List (Block α β)) (x : α) : ℕ :=
  (bs.map (fun b => 1 + count (b.left x) 0 b.size)).prod

def multiplicityRight (bs : List (Block α β)) (y : β) : ℕ :=
  (bs.map (fun b => 1 + count (b.right y) 0 b.size)).prod

theorem chargeLeft_le (n : ℕ) (bs : List (Block α β)) (x : α) :
    chargeLeft n bs x ≤ coefficient n bs * multiplicityLeft bs x := by
  induction bs with
  | nil => simp [chargeLeft, coefficient, multiplicityLeft]
  | cons b rest ih =>
    have hp : 1 ≤ multiplicityLeft rest x := by
      unfold multiplicityLeft
      apply List.one_le_prod
      intro k hk
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hk
      omega
    have hc : 1 ≤ coefficient n rest := by simp [coefficient]; omega
    have hm := Nat.add_le_add (Nat.mul_le_mul_left (2 * depth b) hp) ih
    have hone : 1 ≤ (2 * depth b + coefficient n rest) * multiplicityLeft rest x := by
      have hh : 1 ≤ 2 * depth b + coefficient n rest := by omega
      simpa using Nat.mul_le_mul hh hp
    calc
      chargeLeft n (b :: rest) x =
          1 + (2 * depth b + chargeLeft n rest x) * count (b.left x) 0 b.size := rfl
      _ ≤ 1 + ((2 * depth b + coefficient n rest) * multiplicityLeft rest x) *
          count (b.left x) 0 b.size := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_right
        nlinarith [hm]
      _ ≤ ((2 * depth b + coefficient n rest) * multiplicityLeft rest x) +
          ((2 * depth b + coefficient n rest) * multiplicityLeft rest x) *
            count (b.left x) 0 b.size := Nat.add_le_add_right hone _
      _ = coefficient n (b :: rest) * multiplicityLeft (b :: rest) x := by
        simp only [coefficient, multiplicityLeft, List.map_cons, List.sum_cons, List.prod_cons]
        ring

theorem chargeRight_le (n : ℕ) (bs : List (Block α β)) (y : β) :
    chargeRight n bs y ≤ coefficient n bs * multiplicityRight bs y := by
  induction bs with
  | nil => simp [chargeRight, coefficient, multiplicityRight]
  | cons b rest ih =>
    have hp : 1 ≤ multiplicityRight rest y := by
      unfold multiplicityRight
      apply List.one_le_prod
      intro k hk
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hk
      omega
    have hc : 1 ≤ coefficient n rest := by simp [coefficient]; omega
    have hm := Nat.add_le_add (Nat.mul_le_mul_left (2 * depth b) hp) ih
    have hone : 1 ≤ (2 * depth b + coefficient n rest) * multiplicityRight rest y := by
      have hh : 1 ≤ 2 * depth b + coefficient n rest := by omega
      simpa using Nat.mul_le_mul hh hp
    calc
      chargeRight n (b :: rest) y =
          1 + (2 * depth b + chargeRight n rest y) * count (b.right y) 0 b.size := rfl
      _ ≤ 1 + ((2 * depth b + coefficient n rest) * multiplicityRight rest y) *
          count (b.right y) 0 b.size := by
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_right
        nlinarith [hm]
      _ ≤ ((2 * depth b + coefficient n rest) * multiplicityRight rest y) +
          ((2 * depth b + coefficient n rest) * multiplicityRight rest y) *
            count (b.right y) 0 b.size := Nat.add_le_add_right hone _
      _ = coefficient n (b :: rest) * multiplicityRight (b :: rest) y := by
        simp only [coefficient, multiplicityRight, List.map_cons, List.sum_cons, List.prod_cons]
        ring

theorem scans_le_multiplicities (n : ℕ) (wx : α → ℤ) (wy : β → ℤ) (target : ℤ)
    (bs : List (Block α β)) (xs : List α) (ys : List β) :
    (check n wx wy target bs xs ys).scans ≤ coefficient n bs *
      ((xs.map (multiplicityLeft bs)).sum + (ys.map (multiplicityRight bs)).sum) := by
  have hl : (xs.map (chargeLeft n bs)).sum ≤
      coefficient n bs * (xs.map (multiplicityLeft bs)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      nlinarith [chargeLeft_le n bs x]
  have hr : (ys.map (chargeRight n bs)).sum ≤
      coefficient n bs * (ys.map (multiplicityRight bs)).sum := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      nlinarith [chargeRight_le n bs y]
  have hs := scans_le n wx wy target bs xs ys
  nlinarith

end LowSpaceSubsetSum.SeparatorBlocks

end OAI
