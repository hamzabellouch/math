import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredSortCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CoordinateRowBuild

namespace OAI

/-! # Sorting and retaining one concrete separator coordinate row -/

namespace LowSpaceSubsetSum.CoordinateRowCells

variable {n g : ℕ}

def sorted (xs : List (Fin n)) : (List (Fin n) × ℕ) × ℕ :=
  MeasuredSortCells.run 1 (fun x y : Fin n => ((decide (x ≤ y), 1), 4)) (Nat.clog 2 xs.length) xs

theorem sorted_value (xs : List (Fin n)) : (sorted xs).1 = CoordinateRowBuild.sorted xs := by
  simp only [sorted, MeasuredSortCells.run_value, CoordinateRowBuild.sorted, MeasuredSort.sort]

def run (xs : List (Fin n)) (hg : xs.length = g) : (Vector (Fin n) g × ℕ) × ℕ :=
  let out := sorted xs
  ((⟨out.1.1.toArray, by rw [sorted_value]; simpa only [List.size_toArray, CoordinateRowBuild.sorted_length] using hg⟩,
    out.1.2+xs.length+1), out.2+4*xs.length+16)

theorem value (xs : List (Fin n)) (hg : xs.length = g) :
    (run xs hg).1 = CoordinateRowBuild.run xs hg := by
  simp only [run, CoordinateRowBuild.run, sorted_value]

theorem cells (xs : List (Fin n)) (hg : xs.length = g) (hn : g ≤ n) :
    (run xs hg).2 ≤ 96*(n+1)^2 := by
  have hd : Nat.clog 2 xs.length ≤ n :=
    Nat.clog_le_of_le_pow (hg ▸ hn.trans (Nat.lt_two_pow_self (n := n)).le)
  have hs := MeasuredSortCells.run_cells 1
    (fun x y : Fin n => ((decide (x ≤ y), 1), 4)) 4 (fun _ _ => le_rfl)
    (Nat.clog 2 xs.length) xs
  have hc : 24*(1+2)*(xs.length+1)+4 ≤ 76*(n+1) := by omega
  have hs' := hs.trans (Nat.mul_le_mul (show Nat.clog 2 xs.length+1 ≤ n+1 by omega) hc)
  change _+4*xs.length+16 ≤ _
  dsimp only [sorted]
  nlinarith only [hs', hn, hg, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.CoordinateRowCells

end OAI
