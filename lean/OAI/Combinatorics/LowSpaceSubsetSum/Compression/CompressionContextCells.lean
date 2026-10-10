import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionInitializationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionContext
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredSortCells

namespace OAI

/-! # Preparing a shared compression reader context

Sort the right array once, then initialize rows by reading that same array.
The trace includes the old array, list view and returned sorted array, as
well as the direct tournament construction.
-/

namespace LowSpaceSubsetSum.CompressionContextCells

open CompressionContext (Context)

def compare (P : ℤ) (x y : ℤ) : (Bool × ℕ) × ℕ :=
  (CompressionContext.compare P x y,8)

def sort (P : ℤ) (xs : Array ℤ) : (Array ℤ × ℕ) × ℕ :=
  let out := MeasuredSortCells.run 1 (compare P) (Nat.clog 2 xs.size) xs.toList
  ((out.1.1.toArray,out.1.2+xs.size+1),out.2+3*(xs.size+1)+16)

theorem sort_value (P : ℤ) (xs : Array ℤ) :
    (sort P xs).1 = CompressionContext.sort P xs := by
  simp only [sort, MeasuredSortCells.run_value, compare, CompressionContext.sort,
    MeasuredSort.sort, Array.length_toList]

theorem sort_size (P : ℤ) (xs : Array ℤ) : (sort P xs).1.1.size = xs.size := by
  rw [sort_value, CompressionContext.sort_size]

theorem sort_cells {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (P : ℤ) (xs : Array ℤ) (C : ℕ) (hsize : xs.size ≤ C) (hC : C ≤ 2^n) :
    (sort P xs).2 ≤ inputScale I^3*(C+1) := by
  let u := inputScale I
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hd := Nat.clog_le_of_le_pow (hsize.trans hC)
  have h := MeasuredSortCells.run_cells 1 (compare P) 8 (fun _ _ => le_rfl)
    (Nat.clog 2 xs.size) xs.toList
  simp only [Array.length_toList] at h
  have hcoef : 24*(1+2)*(xs.size+1)+8 ≤ 80*(C+1) := by omega
  have hm := h.trans (Nat.mul_le_mul (show Nat.clog 2 xs.size+1 ≤ u by omega) hcoef)
  have hs : (sort P xs).2 ≤ 100*u*(C+1) := by
    change _+3*(xs.size+1)+16 ≤ _
    nlinarith only [hm,hu,hsize,hn]
  have hp : 100*u ≤ u^3 := by
    have hl : 100 ≤ u^2 := by nlinarith only [hu,hn]
    have hm := Nat.mul_le_mul_right u hl
    simpa only [pow_succ] using hm
  exact hs.trans (Nat.mul_le_mul_right (C+1) hp)

private theorem primary (P : ℤ) (xs : Array ℤ) :
    FilteredRow.PrimarySorted (sort P xs).1.1 id 1 := by
  rw [sort_value, CompressionContext.sort_value]
  exact ResidueSort.primary _ _ _ _

private theorem secondary (P : ℤ) (xs : Array ℤ) :
    FilteredRow.SecondarySorted (sort P xs).1.1 id 1 P := by
  rw [sort_value, CompressionContext.sort_value]
  exact ResidueSort.secondary _ _ _ _

def fromArrays (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) : (Context P mode × ℕ) × ℕ :=
  let out := CompressionInitializationCells.start left right P hs ht hP mode
  ((⟨right,Nat.clog 2 left.size,out.1.1⟩,out.1.2),out.2+4*(left.size+right.size+1)+32)

theorem fromArrays_value (left right : Array ℤ) (P : ℤ)
    (hs : FilteredRow.PrimarySorted right id 1)
    (ht : FilteredRow.SecondarySorted right id 1 P) (hP : 0 < P)
    (mode : FilteredStream.Mode) :
    (fromArrays left right P hs ht hP mode).1 =
      CompressionContext.fromArrays left right P hs ht hP mode := by
  simp only [fromArrays,CompressionInitializationCells.start_value,CompressionContext.fromArrays]

def build (left right : Array ℤ) (P : ℤ) (hP : 0 < P) (mode : FilteredStream.Mode) :
    (Context P mode × ℕ) × ℕ :=
  let sorted := sort P right
  let out := fromArrays left sorted.1.1 P (primary P right) (secondary P right) hP mode
  ((out.1.1,sorted.1.2+out.1.2+2),sorted.2+out.2+4*(left.size+right.size+1)+32)

theorem build_value (left right : Array ℤ) (P : ℤ) (hP : 0 < P) (mode : FilteredStream.Mode) :
    (build left right P hP mode).1 = CompressionContext.build left right P hP mode := by
  simp only [build,fromArrays_value,sort_value,CompressionContext.build]

theorem build_cells {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (left right : Array ℤ) (P : ℤ) (hP : 0 < P) (mode : FilteredStream.Mode)
    (C : ℕ) (hL : left.size ≤ C) (hR : right.size ≤ C) (hC : C ≤ 2^n) :
    (build left right P hP mode).2 ≤ inputScale I^6*(C+1) := by
  let u := inputScale I
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hs := sort_cells I hn P right C hR hC
  have hi := CompressionInitializationCells.start_cells I hn left (sort P right).1.1 P
    (primary P right) (secondary P right) hP mode C hL hC
  have hlen : (sort P right).1.1.size ≤ C := (sort_size P right).le.trans hR
  have hp : u^3 ≤ u^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpoly : 128 ≤ u^5 := by
    have : u ≤ u^5 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega)
        (by decide : 1 ≤ 5)
    omega
  have hm : 4*u^5 ≤ u^6 := by
    calc
      _ ≤ u*u^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change _ ≤ u^6*(C+1)
  change (sort P right).2 + ((CompressionInitializationCells.start left (sort P right).1.1
    P (primary P right) (secondary P right) hP mode).2+
      4*(left.size+(sort P right).1.1.size+1)+32)+4*(left.size+right.size+1)+32 ≤ _
  have hsmall : (sort P right).2 + ((CompressionInitializationCells.start left (sort P right).1.1
    P (primary P right) (secondary P right) hP mode).2+
      4*(left.size+(sort P right).1.1.size+1)+32)+4*(left.size+right.size+1)+32 ≤
      4*u^5*(C+1) := by
    nlinarith only [hs,hi,hL,hR,hlen,hpoly,Nat.mul_le_mul_right (C+1) hp]
  exact hsmall.trans (Nat.mul_le_mul_right (C+1) hm)

end LowSpaceSubsetSum.CompressionContextCells

end OAI
