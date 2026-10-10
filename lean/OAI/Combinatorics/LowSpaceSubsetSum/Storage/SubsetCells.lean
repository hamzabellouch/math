import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedSubsets

namespace OAI

/-! # Memory of concrete subset-family generation

The trace retains the first recursive family while generating the second,
then counts append/map output alongside both families. Its work projection
is exactly the output-sensitive generator.
-/

namespace LowSpaceSubsetSum.SubsetCells

variable {α : Type*}

def all (X : ℕ) : List α → (List (List α) × ℕ) × ℕ
  | [] => (([[]], 1), X + 8)
  | x :: xs =>
    let rest := all X xs
    ((rest.1.1.flatMap (fun S => [S, x :: S]), rest.1.2 + 3 * rest.1.1.length + 1),
      max rest.2 ((X + 1) * (xs.length + 2) * (4 * rest.1.1.length + 4)))

theorem all_value (X : ℕ) (xs : List α) : (all X xs).1 = CountedSubsets.all xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [all, CountedSubsets.all, ih]

theorem all_cells (X : ℕ) (xs : List α) :
    (all X xs).2 ≤ 8 * (X + 1) * (xs.length + 1) * 2 ^ xs.length := by
  induction xs with
  | nil => simp only [all, List.length_nil, Nat.zero_add, Nat.mul_one, pow_zero]; omega
  | cons x xs ih =>
    have hp : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
    have hl : (all X xs).1.1.length = 2 ^ xs.length := by rw [all_value, CountedSubsets.all_length]
    simp only [all, hl, List.length_cons, pow_succ]
    apply max_le
    · exact ih.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left (8 * (X + 1)) (by omega)) (by omega))
    · calc
        _ ≤ (X + 1) * (xs.length + 2) * (16 * 2 ^ xs.length) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring

def select (X k : ℕ) (xs : List α) : (List (List α) × ℕ) × ℕ :=
  match k, xs with
  | 0, xs => (([[]], 1), (X + 1) * (xs.length + 1) + 8)
  | _ + 1, [] => (([], 1), X + 8)
  | k + 1, x :: xs =>
    if k + 1 ≤ xs.length + 1 then
      let left := select X (k + 1) xs
      let right := select X k xs
      ((left.1.1 ++ right.1.1.map (List.cons x),
        left.1.2 + right.1.2 + left.1.1.length + right.1.1.length + xs.length + 2),
        max left.2 (max ((X + 1) * (xs.length + 2) * (left.1.1.length + 1) + right.2)
          ((X + 1) * (xs.length + 2) * (2 * left.1.1.length + 2 * right.1.1.length + 4))))
    else (([], xs.length + 2), (X + 1) * (xs.length + 2) + 8)
termination_by xs.length

theorem select_value (X k : ℕ) (xs : List α) : (select X k xs).1 = CountedSubsets.select k xs := by
  induction xs generalizing k with
  | nil => cases k <;> simp only [select, CountedSubsets.select]
  | cons x xs ih =>
    cases k with
    | zero => simp only [select, CountedSubsets.select]
    | succ k =>
      rw [select, CountedSubsets.select]
      split <;> simp only [ih]

private theorem select_step (X m lw rw ll rl a b : ℕ)
    (ha : a ≤ 16 * (X + 1) * (m + 1) * lw)
    (hb : b ≤ 16 * (X + 1) * (m + 1) * rw) :
    max a (max ((X + 1) * (m + 2) * (ll + 1) + b)
      ((X + 1) * (m + 2) * (2 * ll + 2 * rl + 4))) ≤
      16 * (X + 1) * (m + 2) * (lw + rw + ll + rl + m + 2) := by
  let A := (X + 1) * (m + 2)
  have hcoef : 16 * (X + 1) * (m + 1) ≤ 16 * A := by
    dsimp only [A]
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)
  have ha' := ha.trans (Nat.mul_le_mul_right lw hcoef)
  have hb' := hb.trans (Nat.mul_le_mul_right rw hcoef)
  have he : 16 * (X + 1) * (m + 2) = 16 * A := by dsimp only [A]; ac_rfl
  rw [he]
  change max a (max (A * (ll + 1) + b) (A * (2 * ll + 2 * rl + 4))) ≤ _
  apply max_le
  · exact ha'.trans (Nat.mul_le_mul_left _ (by omega))
  · apply max_le
    · have hmid : A * (ll + 1) ≤ 16 * A * (lw + ll + rl + m + 2) := by
        calc
          _ ≤ A * (16 * (lw + ll + rl + m + 2)) := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ring
      calc
        _ ≤ 16 * A * (lw + ll + rl + m + 2) + 16 * A * rw := Nat.add_le_add hmid hb'
        _ = _ := by ring
    · calc
        _ ≤ A * (16 * (lw + rw + ll + rl + m + 2)) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring

theorem select_cells (X k : ℕ) (xs : List α) :
    (select X k xs).2 ≤ 16 * (X + 1) * (xs.length + 1) * (CountedSubsets.select k xs).2 := by
  induction xs generalizing k with
  | nil => cases k <;> simp only [select, CountedSubsets.select, List.length_nil, Nat.zero_add, Nat.mul_one] <;> omega
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [select, CountedSubsets.select, Nat.mul_one]
      have hp : 1 ≤ (X + 1) * ((x :: xs).length + 1) := Nat.mul_pos (by omega) (by omega)
      rw [Nat.mul_assoc]
      omega
    | succ k =>
      rw [select, CountedSubsets.select]
      split
      · have hl := ih (k + 1)
        have hr := ih k
        have hvl := select_value X (k + 1) xs
        have hvr := select_value X k xs
        dsimp only
        rw [List.length_cons]
        simpa only [hvl, hvr] using select_step X xs.length
          (CountedSubsets.select (k + 1) xs).2 (CountedSubsets.select k xs).2
          (CountedSubsets.select (k + 1) xs).1.length (CountedSubsets.select k xs).1.length _ _ hl hr
      · dsimp only
        simp only [List.length_cons]
        have hp : 1 ≤ (X + 1) * (xs.length + 2) := Nat.mul_pos (by omega) (by omega)
        have hm := Nat.mul_le_mul_left (16 * ((X + 1) * (xs.length + 2)))
          (show 1 ≤ xs.length + 2 by omega)
        simp only [Nat.mul_one] at hm
        simp only [show xs.length + 1 + 1 = xs.length + 2 by omega, Nat.mul_assoc] at hm ⊢
        omega


theorem select_cells_card (X k : ℕ) (xs : List α) (hk : k ≤ xs.length) :
    (select X k xs).2 ≤ 64 * (X + 1) * (xs.length + 1) ^ 3 * xs.length.choose k := by
  calc
    _ ≤ 16 * (X + 1) * (xs.length + 1) * (CountedSubsets.select k xs).2 := select_cells X k xs
    _ ≤ 16 * (X + 1) * (xs.length + 1) *
        (4 * (xs.length + 1) ^ 2 * xs.length.choose k) :=
      Nat.mul_le_mul_left _ (CountedSubsets.select_work k xs hk)
    _ = _ := by ring

end LowSpaceSubsetSum.SubsetCells

end OAI
