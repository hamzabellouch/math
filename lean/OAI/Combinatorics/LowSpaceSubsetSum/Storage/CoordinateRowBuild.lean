import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.TopCoordinatesBlocks

namespace OAI

/-! # Stored coordinate rows from explicit block lists

The executable part sorts a list of ambient indices and copies it to an
array. The finite-set order is used only to identify the resulting row with
the coordinates in the mathematical separator analysis.
-/

namespace LowSpaceSubsetSum.CoordinateRowBuild

variable {n g : ℕ}

def sorted (xs : List (Fin n)) : List (Fin n) × ℕ :=
  MeasuredSort.sort (fun x y : Fin n => (decide (x ≤ y), 1)) xs

theorem sorted_length (xs : List (Fin n)) : (sorted xs).1.length = xs.length := by
  rw [sorted, MeasuredSort.sort_value]
  exact List.Perm.length_eq (List.mergeSort_perm xs _)

theorem sorted_value (xs : List (Fin n)) (hx : xs.Nodup) :
    (sorted xs).1 = xs.toFinset.sort (· ≤ ·) := by
  rw [sorted, MeasuredSort.sort_value]
  have hp := List.mergeSort_perm xs (fun x y => decide (x ≤ y))
  have hs := (List.toFinset_sort (r := (· ≤ ·)) (hp.nodup_iff.mpr hx)).mpr
    (List.pairwise_mergeSort' (· ≤ ·) xs)
  have hset : (xs.mergeSort (fun x y => decide (x ≤ y))).toFinset = xs.toFinset := by
    ext i
    simp only [List.mem_toFinset, hp.mem_iff]
  rw [hset] at hs
  exact hs.symm

def run (xs : List (Fin n)) (hg : xs.length = g) : Vector (Fin n) g × ℕ :=
  let out := sorted xs
  (⟨out.1.toArray, by
      change (sorted xs).1.toArray.size = g
      simpa only [List.size_toArray, sorted_length] using hg⟩,
    out.2 + xs.length + 1)

theorem value (xs : List (Fin n)) (hg : xs.length = g) (hx : xs.Nodup)
    (S : Finset (Fin n)) (hS : xs.toFinset = S) (hcard : S.card = g) (i : Fin g) :
    (run xs hg).1[i.val] = ((S.orderIsoOfFin hcard) i).val := by
  rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [run, Vector.getElem_mk, List.getElem_toArray]
  have hv : (sorted xs).1 = S.sort (· ≤ ·) := by rw [sorted_value xs hx, hS]
  simp only [hv]
  rfl

theorem work (xs : List (Fin n)) (hg : xs.length = g) (hn : g ≤ n) :
    (run xs hg).2 ≤ 16 * (n + 1) ^ 2 := by
  have hs := MeasuredSort.sort_work (fun x y : Fin n => (decide (x ≤ y), 1)) 1
    (fun _ _ => le_rfl) xs n
    (hg ▸ hn.trans (Nat.lt_two_pow_self (n := n)).le)
  change (sorted xs).2 + xs.length + 1 ≤ _
  dsimp only [sorted]
  rw [hg] at hs ⊢
  nlinarith only [hs, hn, Nat.zero_le (n ^ 2)]

end LowSpaceSubsetSum.CoordinateRowBuild

end OAI
