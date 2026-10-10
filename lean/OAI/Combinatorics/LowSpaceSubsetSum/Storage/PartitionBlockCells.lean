import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPartitionBlocks

namespace OAI

/-! # Live arrays and list spines when selecting a labeled block -/

namespace LowSpaceSubsetSum.PartitionBlockCells

variable {n m b : ℕ}

def run (xs : Vector (Fin n) m) (labels : Vector (Fin b) m) (a : Fin b) :
    (List (Fin n) × ℕ) × ℕ :=
  let chosen := MeasuredFilterCells.run
    (fun i : Fin m => ((decide (labels[i.val] = a), 0), 4)) (List.finRange m)
  ((chosen.1.1.map (fun i => xs[i.val]), 5*m+1), chosen.2+6*m+24)

theorem value (xs : Vector (Fin n) m) (labels : Vector (Fin b) m) (a : Fin b) :
    (run xs labels a).1 = StoredPartitionBlocks.run xs labels a := by
  simp only [run, StoredPartitionBlocks.run, StoredPartitionBlocks.block,
    MeasuredFilterCells.run_value, MeasuredFilter.runAcc_value,
    List.reverse_nil, List.nil_append]

theorem length (xs : Vector (Fin n) m) (labels : Vector (Fin b) m) (a : Fin b) :
    (run xs labels a).1.1.length ≤ m := by
  rw [value]
  change ((List.finRange m).filter _ |>.map _).length ≤ m
  simpa only [List.length_map, List.length_finRange] using List.length_filter_le _ (List.finRange m)

theorem cells (xs : Vector (Fin n) m) (labels : Vector (Fin b) m) (a : Fin b) :
    (run xs labels a).2 ≤ 8*m+32 := by
  have h := MeasuredFilterCells.run_cells
    (fun i : Fin m => ((decide (labels[i.val] = a), 0), 4)) 4 (fun _ => le_rfl) (List.finRange m)
  simp only [List.length_finRange] at h
  change _+6*m+24 ≤ _
  omega

end LowSpaceSubsetSum.PartitionBlockCells

end OAI
