import OAI.Combinatorics.LowSpaceSubsetSum.Storage.IntervalDomainExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredSortCells

namespace OAI

/-! # Live storage for arithmetic interval domain construction

The scan tests only the two interval endpoints. It filters the bounded
index list, looks up the stored permutation, and sorts the resulting
indices. The immutable permutation array is shared throughout.
-/

namespace LowSpaceSubsetSum.IntervalDomainCells

variable {n : ℕ}

def test (start len : ℕ) (i : Fin n) : (Bool × ℕ) × ℕ :=
  ((decide (start ≤ i.val ∧ i.val < start+len), 2), 8)

def positions (n start len : ℕ) : List (Fin n) × ℕ :=
  let r := MeasuredFilterCells.run (test start len) (List.finRange n)
  (r.1.1, r.2+2*n+8)

theorem positions_value (n start len : ℕ) :
    (positions n start len).1 = IntervalDomainExecution.positions n start len := by
  simp only [positions, MeasuredFilterCells.run_value, MeasuredFilter.runAcc_value,
    List.reverse_nil, List.nil_append, test, IntervalDomainExecution.positions]

theorem positions_length (n start len : ℕ) : (positions n start len).1.length ≤ n := by
  rw [positions_value]
  simpa only [IntervalDomainExecution.positions, List.length_finRange] using
    List.length_filter_le (fun i : Fin n => decide (start ≤ i.val ∧ i.val < start+len))
      (List.finRange n)

theorem positions_length_interval (n start len : ℕ) (h : start+len ≤ n) :
    (positions n start len).1.length = len := by
  rw [positions_value]
  have hn := (List.nodup_finRange n).filter
    (fun i : Fin n => decide (start ≤ i.val ∧ i.val < start+len))
  have hs : (IntervalDomainExecution.positions n start len).toFinset =
      indexInterval n start len := by
    ext i
    simp only [IntervalDomainExecution.positions, List.mem_toFinset, List.mem_filter,
      List.mem_finRange, true_and, decide_eq_true_eq, indexInterval, Finset.mem_filter,
      Finset.mem_univ]
  have hc := List.toFinset_card_of_nodup hn
  change (IntervalDomainExecution.positions n start len).toFinset.card =
    (IntervalDomainExecution.positions n start len).length at hc
  rw [hs, indexInterval_card h] at hc
  exact hc.symm

theorem positions_cells (n start len : ℕ) : (positions n start len).2 ≤ 4*n+20 := by
  have h := MeasuredFilterCells.run_cells (test start len) 8 (fun _ => le_rfl) (List.finRange n)
  simp only [List.length_finRange] at h
  change _+2*n+8 ≤ _
  omega

def map (v : Vector (Fin n) n) : List (Fin n) → List (Fin n) × ℕ
  | [] => ([], 4)
  | i :: xs =>
    let r := map v xs
    (v[i.val]::r.1, r.2+8)

theorem map_value (v : Vector (Fin n) n) (xs : List (Fin n)) :
    (map v xs).1 = xs.map (fun i => v[i.val]) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [map, List.map_cons, ih]

theorem map_cells (v : Vector (Fin n) n) (xs : List (Fin n)) :
    (map v xs).2 ≤ 8*xs.length+4 := by
  induction xs with
  | nil => exact le_rfl
  | cons i xs ih => simp only [map, List.length_cons]; omega

def compare (x y : Fin n) : (Bool × ℕ) × ℕ := ((decide (x ≤ y), 1), 4)

def run (v : Vector (Fin n) n) (start len : ℕ) : (List (Fin n) × ℕ) × ℕ :=
  let ps := positions n start len
  let xs := map v ps.1
  let sorted := MeasuredSortCells.run 1 compare (Nat.clog 2 xs.1.length) xs.1
  ((sorted.1.1, sorted.1.2+8*(n+1)^2), ps.2+xs.2+sorted.2+4*(n+1))

theorem run_value (v : Vector (Fin n) n) (start len : ℕ) :
    (run v start len).1 = IntervalDomainExecution.run v start len := by
  simp only [run, MeasuredSortCells.run_value, map_value, positions_value,
    IntervalDomainExecution.run, MeasuredSort.sort, compare]

theorem run_length (v : Vector (Fin n) n) (start len : ℕ) (h : start+len ≤ n) :
    (run v start len).1.1.length = len := by
  rw [run_value]
  simp only [IntervalDomainExecution.run, MeasuredSort.sort_value, List.length_mergeSort,
    List.length_map]
  simpa only [positions_value] using positions_length_interval n start len h

theorem run_cells (v : Vector (Fin n) n) (start len : ℕ) :
    (run v start len).2 ≤ 128*(n+1)^2 := by
  let ps := positions n start len
  let xs := map v ps.1
  have hp := positions_cells n start len
  have hm := map_cells v ps.1
  have hl := positions_length n start len
  have hxs : xs.1.length ≤ n := by
    dsimp only [xs]
    rw [map_value, List.length_map]
    exact hl
  have hd : Nat.clog 2 xs.1.length ≤ n :=
    Nat.clog_le_of_le_pow (hxs.trans (Nat.lt_two_pow_self (n := n)).le)
  have hs := MeasuredSortCells.run_cells 1 compare 4 (fun _ _ => le_rfl)
    (Nat.clog 2 xs.1.length) xs.1
  have hcoef : 24*(1+2)*(xs.1.length+1)+4 ≤ 76*(n+1) := by omega
  have hs' := hs.trans (Nat.mul_le_mul (show Nat.clog 2 xs.1.length+1 ≤ n+1 by omega) hcoef)
  change ps.2+xs.2+_+4*(n+1) ≤ _
  change ps.2 ≤ _ at hp
  change xs.2 ≤ _ at hm
  change ps.1.length ≤ n at hl
  nlinarith only [hp, hm, hl, hs']

end LowSpaceSubsetSum.IntervalDomainCells

end OAI
