import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FiniteSetCells

namespace OAI

/-! # Finite-set metadata built from a stored list

Insertion first scans the current set through its quotient-invariant stored
list. The tail loop retains only the current set, input suffix and scalar
counters; duplicate occurrences do not enlarge the set.
-/

namespace LowSpaceSubsetSum.ListSetCells

variable {n : ℕ}

def insert (x : Fin n) (s : Finset (Fin n)) : (Finset (Fin n) × ℕ) × ℕ :=
  let seen := FiniteSetCells.member s x
  ((if seen.1.1 then s else Insert.insert x s, seen.1.2+2*s.card+2), 4*s.card+24)

theorem insert_value (x : Fin n) (s : Finset (Fin n)) :
    (insert x s).1.1 = Insert.insert x s := by
  simp only [insert, FiniteSetCells.member_formula]
  by_cases h : x ∈ s
  · simp only [h, decide_true, ↓reduceIte, Finset.insert_eq_of_mem h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem insert_work (x : Fin n) (s : Finset (Fin n)) :
    (insert x s).1.2 = 3*s.card+3 := by
  simp only [insert, FiniteSetCells.member_formula]
  omega

def loop : List (Fin n) → Finset (Fin n) → ℕ → ℕ → (Finset (Fin n) × ℕ) × ℕ
  | [], s, work, peak => ((s, work+1), max peak (4*s.card+32))
  | x :: xs, s, work, peak =>
    let next := insert x s
    loop xs next.1.1 (work+next.1.2)
      (max peak (4*(xs.length+s.card+1)+next.2+32))

theorem loop_value (xs : List (Fin n)) (s : Finset (Fin n)) (work peak : ℕ) :
    (loop xs s work peak).1.1 = s ∪ xs.toFinset := by
  induction xs generalizing s work peak with
  | nil => simp only [loop, List.toFinset_nil, Finset.union_empty]
  | cons x xs ih =>
    simp only [loop, ih, insert_value, List.toFinset_cons]
    ext y
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

theorem loop_work (xs : List (Fin n)) (s : Finset (Fin n)) (work peak : ℕ) :
    (loop xs s work peak).1.2 ≤ work+3*(xs.length+s.card+1)*xs.length+1 := by
  induction xs generalizing s work peak with
  | nil => simp only [loop, List.length_nil, Nat.mul_zero, Nat.add_zero, le_refl]
  | cons x xs ih =>
    have hc : (insert x s).1.1.card ≤ s.card+1 := by
      rw [insert_value]
      exact Finset.card_insert_le x s
    have h := ih (insert x s).1.1 (work+(insert x s).1.2)
      (max peak (4*(xs.length+s.card+1)+(insert x s).2+32))
    simp only [insert_work] at h
    change (loop xs _ _ _).1.2 ≤ _
    simp only [List.length_cons, insert_work]
    nlinarith only [h, hc]

theorem loop_cells (xs : List (Fin n)) (s : Finset (Fin n)) (work peak : ℕ) :
    (loop xs s work peak).2 ≤ max peak (8*(xs.length+s.card)+64) := by
  induction xs generalizing s work peak with
  | nil => simp only [loop, List.length_nil, Nat.zero_add]; exact max_le_max le_rfl (by omega)
  | cons x xs ih =>
    have hc : (insert x s).1.1.card ≤ s.card+1 := by
      rw [insert_value]
      exact Finset.card_insert_le x s
    have h := ih (insert x s).1.1 (work+(insert x s).1.2)
      (max peak (4*(xs.length+s.card+1)+(insert x s).2+32))
    change (loop xs _ _ _).2 ≤ _
    simp only [List.length_cons, insert] at h hc ⊢
    omega

def run (xs : List (Fin n)) : (Finset (Fin n) × ℕ) × ℕ := loop xs ∅ 0 0

theorem value (xs : List (Fin n)) : (run xs).1.1 = xs.toFinset := by
  simpa only [run, Finset.empty_union] using loop_value xs ∅ 0 0

theorem work (xs : List (Fin n)) : (run xs).1.2 ≤ 3*(xs.length+1)*xs.length+1 := by
  simpa only [run, Finset.card_empty, Nat.add_zero, Nat.zero_add] using loop_work xs ∅ 0 0

theorem cells (xs : List (Fin n)) : (run xs).2 ≤ 8*xs.length+64 := by
  simpa only [run, Finset.card_empty, Nat.add_zero, Nat.zero_max] using loop_cells xs ∅ 0 0

theorem three_work (xs ys zs : List (Fin n)) :
    (run xs).1.2+(run ys).1.2+(run zs).1.2 ≤ 4*(xs.length+ys.length+zs.length+1)^2 := by
  have hx := work xs
  have hy := work ys
  have hz := work zs
  nlinarith only [hx, hy, hz, Nat.zero_le (xs.length*ys.length),
    Nat.zero_le (xs.length*zs.length), Nat.zero_le (ys.length*zs.length),
    Nat.zero_le (xs.length^2), Nat.zero_le (ys.length^2), Nat.zero_le (zs.length^2)]

end LowSpaceSubsetSum.ListSetCells

end OAI
