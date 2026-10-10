import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CoordinateBlocksCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionBlockCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredCoordinatePreparation

namespace OAI

/-! # Guarded coordinate arrays with their block-selection storage -/

namespace LowSpaceSubsetSum.StoredCoordinateCells

open scoped BigOperators
variable {n : ℕ}

def run (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n) :
    (Option (StoredCoordinatePreparation.Rows n) × ℕ) × ℕ :=
  let blocks := Vector.ofFn (fun a : Fin 4 => PartitionBlockCells.run (domains 0) (labels 0) a)
  if h : ∀ a : Fin 4, blocks[a.val].1.1.length = StoredTopCoordinates.width n then
    let out := CoordinateBlocksCells.run (fun a => blocks[a.val].1.1) h
    ((some out.1.1, out.1.2+40*PartitionLabelExecution.size n 0+17),
      (∑ a : Fin 4, blocks[a.val].2)+out.2+12*n+96)
  else ((none, 20*PartitionLabelExecution.size n 0+8),
    (∑ a : Fin 4, blocks[a.val].2)+12*n+96)

theorem value (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n) :
    (run domains labels).1 = StoredCoordinatePreparation.run domains labels := by
  have hb (a : Fin 4) : (PartitionBlockCells.run (domains 0) (labels 0) a).1.1 =
      StoredPartitionBlocks.block (domains 0) (labels 0) a :=
    congrArg Prod.fst (PartitionBlockCells.value (domains 0) (labels 0) a)
  simp only [run, Vector.getElem_ofFn, Fin.eta, hb, CoordinateBlocksCells.value,
    StoredCoordinatePreparation.run, StoredTopCoordinates.run]
  split
  · simp_all only [Nat.add_assoc]
    apply Prod.ext
    · rfl
    · omega
  · simp_all only

theorem cells (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n) :
    (run domains labels).2 ≤ 1024*(n+1)^2 := by
  have hm : PartitionLabelExecution.size n 0 ≤ n := by
    unfold PartitionLabelExecution.size RepresentationSetup.blockCount RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  have hg : StoredTopCoordinates.width n ≤ n := by
    unfold StoredTopCoordinates.width RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  have hb := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 4))) =>
    PartitionBlockCells.cells (domains 0) (labels 0) a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
  unfold run
  dsimp only
  split
  next h =>
    have hc := CoordinateBlocksCells.cells
      (fun a : Fin 4 => (PartitionBlockCells.run (domains 0) (labels 0) a).1.1)
      (by simpa only [Vector.getElem_ofFn, Fin.eta] using h) hg
    simp only [Vector.getElem_ofFn, Fin.eta]
    nlinarith only [hb, hm, hc, Nat.zero_le (n^2)]
  · simp only [Vector.getElem_ofFn, Fin.eta]
    nlinarith only [hb, hm, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.StoredCoordinateCells

end OAI
