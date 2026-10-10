import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort

namespace OAI

/-! # Compression contexts retaining the actual sorted right array -/

namespace LowSpaceSubsetSum.CompressionContext

structure Context (P : ℤ) (mode : FilteredStream.Mode) where
  right : Array ℤ
  depth : ℕ
  state : CompressionReader.State P mode right depth

def fromArrays (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) : Context P mode × ℕ :=
  let out := CompressionInitialization.start left right P hs ht hP mode
  (⟨right, Nat.clog 2 left.size, out.1⟩, out.2)

theorem fromArrays_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (fromArrays left right P hs ht hP mode).1 =
      ⟨right, Nat.clog 2 left.size, FilteredStream.start left right id id 1 P 0 hs ht hP mode⟩ := by
  simp only [fromArrays, CompressionInitialization.start_value]

def compare (P : ℤ) (x y : ℤ) : Bool × ℕ :=
  (decide (ResidueSort.relation id 1 P x y), 7)

def sort (P : ℤ) (xs : Array ℤ) : Array ℤ × ℕ :=
  let out := MeasuredSort.sort (compare P) xs.toList
  (out.1.toArray, out.2 + xs.size + 1)

theorem sort_value (P : ℤ) (xs : Array ℤ) :
    (sort P xs).1 = ResidueSort.sort xs id 1 P := by
  simp only [sort, MeasuredSort.sort_value, compare, ResidueSort.sort]

theorem sort_size (P : ℤ) (xs : Array ℤ) : (sort P xs).1.size = xs.size := by
  rw [sort_value]
  simp only [ResidueSort.sort, List.size_toArray, List.length_mergeSort, Array.length_toList]

private theorem sorted_primary (P : ℤ) (xs : Array ℤ) :
    FilteredRow.PrimarySorted (sort P xs).1 id 1 := by
  rw [sort_value]
  exact ResidueSort.primary _ _ _ _

private theorem sorted_secondary (P : ℤ) (xs : Array ℤ) :
    FilteredRow.SecondarySorted (sort P xs).1 id 1 P := by
  rw [sort_value]
  exact ResidueSort.secondary _ _ _ _

def build (left right : Array ℤ) (P : ℤ) (hP : 0 < P)
    (mode : FilteredStream.Mode) : Context P mode × ℕ :=
  let sorted := sort P right
  let out := fromArrays left sorted.1 P (sorted_primary P right) (sorted_secondary P right) hP mode
  (out.1, sorted.2 + out.2 + 2)

theorem build_value (left right : Array ℤ) (P : ℤ) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (build left right P hP mode).1 =
      ⟨ResidueSort.sort right id 1 P, Nat.clog 2 left.size,
        FilteredStream.sortedStart left right id id 1 P 0 hP mode⟩ := by
  simp only [build, fromArrays_value, sort_value, FilteredStream.sortedStart]

theorem fromArrays_work {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) (hL : left.size ≤ 2 ^ n) (hR : right.size ≤ 2 ^ n) :
    (fromArrays left right P hs ht hP mode).2 ≤ inputScale I ^ 4 * (left.size + 1) :=
  CompressionInitialization.start_work I hn left right P hs ht hP mode hL hR

theorem sort_work {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (P : ℤ) (xs : Array ℤ) (hsize : xs.size ≤ 2 ^ n) :
    (sort P xs).2 ≤ inputScale I ^ 2 * (xs.size + 1) := by
  have hs := MeasuredSort.sort_work (compare P) 7 (fun _ _ => le_rfl) xs.toList n
    (by simpa only [Array.length_toList] using hsize)
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 8 * (6 * n + 1) + 10 ≤ inputScale I ^ 2 := by nlinarith only [hu, hnu]
  change (MeasuredSort.sort (compare P) xs.toList).2 + xs.size + 1 ≤ _
  simp only [Array.length_toList] at hs
  have hm := Nat.mul_le_mul_right (xs.size + 1) hcoef
  nlinarith only [hs, hm]

theorem build_work {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (left right : Array ℤ) (P : ℤ) (hP : 0 < P)
    (mode : FilteredStream.Mode) (hL : left.size ≤ 2 ^ n) (hR : right.size ≤ 2 ^ n) :
    (build left right P hP mode).2 ≤ inputScale I ^ 5 * (left.size + right.size + 1) := by
  have hs := sort_work I hn P right hR
  have hi := fromArrays_work I hn left (sort P right).1 P
    (sorted_primary P right) (sorted_secondary P right) hP mode hL (by rwa [sort_size])
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : inputScale I ^ 2 ≤ inputScale I ^ 4 :=
    pow_le_pow_right' (by omega : 1 ≤ inputScale I) (by decide : 2 ≤ 4)
  have h1 : 1 ≤ inputScale I ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hm : 4 * inputScale I ^ 4 ≤ inputScale I ^ 5 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change (sort P right).2 + (fromArrays left (sort P right).1 P
    (sorted_primary P right) (sorted_secondary P right) hP mode).2 + 2 ≤ _
  nlinarith only [hs, hi, hp, h1, Nat.mul_le_mul_right (left.size + right.size + 1) hm]

end LowSpaceSubsetSum.CompressionContext

end OAI
