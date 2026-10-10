import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredSortCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRecordSort
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells

namespace OAI

/-! # Stored-record sorting with explicit live-cell accounting

The comparison function executes both bounded-list weight evaluations. The array,
its list view, merge recursion, and final array allocation are included.
-/

namespace LowSpaceSubsetSum.RepresentationSortCells

variable {n : ℕ}

def compare (I : Instance n) (F : IndexedMask n) (p P : ℤ) (x y : LeafRecord n) :
    (Bool × ℕ) × ℕ :=
  let a := RepresentationKeyCells.leafWeight I F x
  let b := RepresentationKeyCells.leafWeight I F y
  ((decide (a.1.1 % p < b.1.1 % p ∨ a.1.1 % p = b.1.1 % p ∧ a.1.1 % P ≤ b.1.1 % P),
    a.1.2 + b.1.2 + 6), max a.2 b.2 + 2 * (3 * n + 4) + 12)

theorem compare_value (I : Instance n) (F : IndexedMask n) (p P : ℤ) (x y : LeafRecord n) :
    (compare I F p P x y).1 = RepresentationKeys.compare I F p P x y := by
  simp only [compare, RepresentationKeyCells.leafWeight_value, RepresentationKeys.compare]

theorem compare_cells (I : Instance n) (F : IndexedMask n) (p P : ℤ) (x y : LeafRecord n) :
    (compare I F p P x y).2 ≤ 62 * inputScale I := by
  have hx := RepresentationKeyCells.leafWeight_cells I F x
  have hy := RepresentationKeyCells.leafWeight_cells I F y
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  change max _ _ + _ + _ ≤ _
  omega

def sort (I : Instance n) (F : IndexedMask n) (p P : ℤ) (xs : Array (LeafRecord n)) :
    (Array (LeafRecord n) × ℕ) × ℕ :=
  let out := MeasuredSortCells.run (3 * n + 4) (compare I F p P) (Nat.clog 2 xs.size) xs.toList
  ((out.1.1.toArray, out.1.2 + xs.size), out.2 + (3 * n + 4) * (3 * xs.size + 3) + 16)

theorem sort_value (I : Instance n) (F : IndexedMask n) (p P : ℤ) (xs : Array (LeafRecord n)) :
    (sort I F p P xs).1 = RepresentationKeys.sort I F p P xs := by
  have he : (fun x y => (compare I F p P x y).1) = RepresentationKeys.compare I F p P := by
    funext x y
    exact compare_value I F p P x y
  simp only [sort, MeasuredSortCells.run_value, he, RepresentationKeys.sort, MeasuredSort.sort,
    Array.length_toList]

private theorem bound (n u N C d a : ℕ) (hn : 10000 ≤ n) (hu : n + 1 ≤ u) (hN : N ≤ C)
    (hd : d ≤ n)
    (ha : a ≤ (d + 1) * (24 * (3 * n + 4 + 2) * (N + 1) + 62 * u)) :
    a + (3 * n + 4) * (3 * N + 3) + 16 ≤ u ^ 5 * (C + 1) := by
  have hX : 3 * n + 6 ≤ 6 * u := by omega
  have h1 : 1 ≤ C + 1 := by omega
  have hU : 1 ≤ u := by omega
  have hcoef : 24 * (3 * n + 6) * (N + 1) + 62 * u ≤ 206 * u * (C + 1) := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 24 hX) (Nat.add_le_add_right hN 1)
    nlinarith only [h, h1, hU]
  have hA := ha.trans (Nat.mul_le_mul (show d + 1 ≤ u by omega) hcoef)
  have hB := Nat.mul_le_mul (show 3 * n + 4 ≤ 4 * u by omega)
    (show 3 * N + 3 ≤ 3 * (C + 1) by omega)
  have hsmall : a + (3 * n + 4) * (3 * N + 3) + 16 ≤ 234 * u ^ 2 * (C + 1) := by
    have hsq : u ≤ u ^ 2 := by nlinarith only [hU]
    nlinarith only [hA, hB, hsq, hU, h1]
  have hpow : 234 * u ^ 2 ≤ u ^ 5 := by
    have hlarge : 234 ≤ u ^ 3 := by
      have h : u ≤ u ^ 3 := by
        simpa only [pow_one] using Nat.pow_le_pow_right hU (by decide : 1 ≤ 3)
      omega
    calc
      _ ≤ u ^ 3 * u ^ 2 := Nat.mul_le_mul_right _ hlarge
      _ = _ := by rw [← pow_add]
  exact hsmall.trans (Nat.mul_le_mul_right (C + 1) hpow)

theorem sort_cells (I : Instance n) (F : IndexedMask n) (p P : ℤ) (xs : Array (LeafRecord n))
    (C : ℕ) (hn : 10000 ≤ n) (hsize : xs.size ≤ C) (hC : C ≤ 2 ^ n) :
    (sort I F p P xs).2 ≤ inputScale I ^ 5 * (C + 1) := by
  have h := MeasuredSortCells.run_cells (3 * n + 4) (compare I F p P) (62 * inputScale I)
    (compare_cells I F p P) (Nat.clog 2 xs.size) xs.toList
  simp only [Array.length_toList] at h
  have hd := Nat.clog_le_of_le_pow (hsize.trans hC)
  exact bound n (inputScale I) xs.size C (Nat.clog 2 xs.size) _ hn
    (by unfold inputScale; omega) hsize hd h

end LowSpaceSubsetSum.RepresentationSortCells

end OAI
