import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerWeightCells

namespace OAI

/-! # Live storage of compression's compact weight lists

Raw subset masks and their weights use the concrete list generator. The
sorted list is compacted by adjacent comparisons, retaining its existing
linear work counter and accounting for each recursive return frame.
-/

namespace LowSpaceSubsetSum.CompressionWeightCells

variable {n : ℕ}

def tail (previous : ℤ) : List ℤ → (List ℤ × ℕ) × ℕ
  | [] => (([previous], 1), 4)
  | x :: xs =>
    if previous = x then
      let rest := tail previous xs
      ((rest.1.1, rest.1.2+1), rest.2+2)
    else
      let rest := tail x xs
      ((previous::rest.1.1, rest.1.2+1), rest.2+4)

theorem tail_value (previous : ℤ) (xs : List ℤ) :
    (tail previous xs).1 = CountedDedup.tail previous xs := by
  induction xs generalizing previous with
  | nil => rfl
  | cons x xs ih =>
    simp only [tail, CountedDedup.tail]
    split <;> simp only [ih]

theorem tail_cells (previous : ℤ) (xs : List ℤ) :
    (tail previous xs).2 ≤ 4*xs.length+4 := by
  induction xs generalizing previous with
  | nil => exact le_rfl
  | cons x xs ih =>
    have h₁ := ih previous
    have h₂ := ih x
    simp only [tail, List.length_cons]
    split <;> dsimp only <;> omega

def dedup : List ℤ → (List ℤ × ℕ) × ℕ
  | [] => (([], 1), 4)
  | x :: xs => tail x xs

theorem dedup_value (xs : List ℤ) : (dedup xs).1 = CountedDedup.run xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact tail_value x xs

theorem dedup_cells (xs : List ℤ) : (dedup xs).2 ≤ 4*xs.length+4 := by
  cases xs with
  | nil => exact le_rfl
  | cons x xs =>
    have h := tail_cells x xs
    simp only [dedup, List.length_cons]
    omega

def compact (a : Fin n → ℤ) (indices : List (Fin n)) : (List ℤ × ℕ) × ℕ :=
  let initial := MixerWeightCells.raw a indices
  let sorted := MeasuredSortCells.run 1 MixerWeightCells.compare
    (Nat.clog 2 initial.1.1.length) initial.1.1
  let out := dedup sorted.1.1
  ((out.1.1, initial.1.2+sorted.1.2+out.1.2+1),
    initial.2+sorted.2+out.2+4*(initial.1.1.length+1)+32)

theorem compact_value (a : Fin n → ℤ) (indices : List (Fin n)) :
    (compact a indices).1 = CompressionWeights.compact a indices := by
  simp only [compact, MixerWeightCells.raw_value, MeasuredSortCells.run_value,
    dedup_value, CompressionWeights.compact, MeasuredSort.sort, MixerWeightCells.compare]

theorem compact_cells (a : Fin n → ℤ) (indices : List (Fin n))
    (hi : indices.length ≤ n) :
    (compact a indices).2 ≤ 512*(n+2)^2*(2^indices.length+1) := by
  have hr := MixerWeightCells.raw_cells a indices hi
  have hl : (MixerWeightCells.raw a indices).1.1.length = 2^indices.length := by
    rw [MixerWeightCells.raw_value, CompressionWeights.raw_length]
  have hs := MeasuredSortCells.run_cells 1 MixerWeightCells.compare 4 (fun _ _ => le_rfl)
    (Nat.clog 2 (MixerWeightCells.raw a indices).1.1.length)
    (MixerWeightCells.raw a indices).1.1
  have hd := dedup_cells (MeasuredSortCells.run 1 MixerWeightCells.compare
    (Nat.clog 2 (MixerWeightCells.raw a indices).1.1.length)
    (MixerWeightCells.raw a indices).1.1).1.1
  rw [MeasuredSortCells.run_length, hl] at hd
  simp only [hl, Nat.clog_pow 2 _ (by decide)] at hs
  have hs' := hs.trans (Nat.mul_le_mul (show indices.length+1 ≤ n+2 by omega)
    (show 24*(1+2)*(2^indices.length+1)+4 ≤ 76*(2^indices.length+1) by omega))
  have hsmall : 4*(2^indices.length+1)+32 ≤ 20*(n+2)*(2^indices.length+1) := by
    have hN : 1 ≤ 2^indices.length := Nat.one_le_two_pow
    nlinarith only [hN]
  have hdegree : n+2 ≤ (n+2)^2 := by nlinarith
  have hfinal := Nat.mul_le_mul_right (2^indices.length+1) hdegree
  change _+_+_+4*((MixerWeightCells.raw a indices).1.1.length+1)+32 ≤ _
  rw [hl]
  simp only [Nat.clog_pow 2 _ (by decide)] at hd ⊢
  simp only [Nat.mul_assoc] at hr hs' hsmall hfinal ⊢
  nlinarith only [hr, hs', hd, hsmall, hfinal]

end LowSpaceSubsetSum.CompressionWeightCells

end OAI
