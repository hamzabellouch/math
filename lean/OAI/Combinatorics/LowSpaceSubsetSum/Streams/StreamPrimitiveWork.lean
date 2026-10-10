import OAI.Combinatorics.LowSpaceSubsetSum.Streams.BinaryPivot
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedSort
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafSpace

namespace OAI

/-! # Counted binary searches and residue sorting

The counted routines follow the same branches as the executable
search and sort. Their first components agree exactly with those routines.
The counters charge predicate calls and merge/split operations, respectively;
word arithmetic and mask access still require separate compilation charges.
-/

namespace LowSpaceSubsetSum

namespace BinaryPivot

def counted {n : ℕ} (p : Fin n → Bool) : ℕ → Cut n → Cut n × ℕ
  | 0, c => (c, 0)
  | k + 1, c =>
    let queried := if c.lo < c.hi then 1 else 0
    let rest := counted p k (step p c)
    (rest.1, queried + rest.2)

theorem counted_value {n : ℕ} (p : Fin n → Bool) (k : ℕ) (c : Cut n) :
    (counted p k c).1 = (step p)^[k] c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => simpa only [counted, Function.iterate_succ_apply] using ih (step p c)

theorem counted_queries {n : ℕ} (p : Fin n → Bool) (k : ℕ) (c : Cut n) :
    (counted p k c).2 ≤ k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    have h := ih (step p c)
    simp only [counted]
    split <;> omega

def countedSearch {n : ℕ} (p : Fin n → Bool) (k : ℕ) : Cut n × ℕ :=
  counted p k (initial n)

theorem countedSearch_value {n : ℕ} (p : Fin n → Bool) (k : ℕ) :
    (countedSearch p k).1 = search p k := counted_value p k (initial n)

theorem countedSearch_queries {n : ℕ} (p : Fin n → Bool) (k : ℕ) :
    (countedSearch p k).2 ≤ k := counted_queries p k (initial n)

end BinaryPivot

namespace ResidueSort

variable {α : Type*}

def counted (xs : Array α) (w : α → ℤ) (p P : ℤ) : Array α × ℕ :=
  let r := CountedSort.sort (fun x y => decide (relation w p P x y)) xs.toList
  (r.1.toArray, r.2)

theorem counted_value (xs : Array α) (w : α → ℤ) (p P : ℤ) :
    (counted xs w p P).1 = sort xs w p P := by
  simp only [counted, CountedSort.sort_value, sort]

theorem counted_work (xs : Array α) (w : α → ℤ) (p P : ℤ) (n : ℕ)
    (hn : xs.size ≤ 2 ^ n) :
    (counted xs w p P).2 ≤ (6 * n + 1) * xs.size + 1 := by
  exact CountedSort.sort_steps_of_index_bits _ xs.toList n (by simpa using hn)

end ResidueSort

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

theorem counted_sort_value :
    (ResidueSort.counted D.rightArray D.wl D.lowModulus D.modulus).1 = D.storedRight :=
  ResidueSort.counted_value _ _ _ _

theorem counted_sort_work (hR : D.rightArray.size ≤ 2 ^ n) :
    (ResidueSort.counted D.rightArray D.wl D.lowModulus D.modulus).2 ≤
      (6 * n + 1) * D.right.occurrences.card + 1 := by
  exact (ResidueSort.counted_work _ _ _ _ n hR).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ D.rightArray_size_le) 1)

theorem any_state_comparisons (hL : D.leftArray.size ≤ 2 ^ n) (s : D.State) :
    MergedReader.advanceComparisons
      (FilteredStream.key D.wl D.wl D.modulus D.mode)
      (FilteredStream.view D.storedRight) s ≤ n :=
  (D.reader_comparisons_le s).trans (Nat.clog_le_of_le_pow hL)

end RepresentationPairData
end LowSpaceSubsetSum

end OAI
