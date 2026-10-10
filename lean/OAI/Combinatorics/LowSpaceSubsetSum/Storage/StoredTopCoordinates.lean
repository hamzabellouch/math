import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPartitionBlocks

namespace OAI

/-! # Separator coordinate rows built from sampled stored labels -/

namespace LowSpaceSubsetSum.StoredTopCoordinates

variable {n : ℕ}

abbrev width (n : ℕ) := 2 * RepresentationSetup.blockHalf n 0

def run (xs : Vector (Fin n) (PartitionLabelExecution.size n 0))
    (labels : PartitionArrayExecution.Labels n 0)
    (hl : ∀ a : Fin 4, (StoredPartitionBlocks.block xs labels a).length = width n) :
    (Fin 4 → Vector (Fin n) (width n)) × ℕ :=
  let rows := CoordinateBlocksBuild.run (fun a => StoredPartitionBlocks.block xs labels a) hl
  (rows.1, rows.2 + 20 * PartitionLabelExecution.size n 0 + 9)

theorem value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (f : R.Partitions z) (xs : Vector (Fin n) (PartitionLabelExecution.size n 0))
    (labels : PartitionArrayExecution.Labels n 0)
    (hx : ∀ k, xs[k.val] = ((CanonicalPartition.ranks R z 0).symm k).val)
    (hf : ∀ k, labels[k.val] = (f 0).val ((CanonicalPartition.ranks R z 0).symm k))
    (hl : ∀ a : Fin 4, (StoredPartitionBlocks.block xs labels a).length = width n)
    (a : Fin 4) (k : Fin (width n)) :
    ((run xs labels hl).1 a)[k.val] = (R.topCoordinates z f).index (a, k) := by
  have hi : Function.Injective (fun k : Fin (PartitionLabelExecution.size n 0) => xs[k.val]) := by
    intro k l h
    apply (CanonicalPartition.ranks R z 0).symm.injective
    apply Subtype.ext
    simpa only [← hx] using h
  exact CoordinateBlocksBuild.value (fun a => StoredPartitionBlocks.block xs labels a) hl
    (fun a => StoredPartitionBlocks.nodup xs labels a hi)
    (fun a => R.rawPartitionBlock z f 0 a.val)
    (fun a => StoredPartitionBlocks.source R z f 0 xs labels hx hf a)
    (fun a => R.rawPartitionBlock_card z f 0 a)
    (fun a b hab => R.rawPartitionBlock_disjoint z f 0 (fun h => hab (Fin.ext h))) a k

theorem work (xs : Vector (Fin n) (PartitionLabelExecution.size n 0))
    (labels : PartitionArrayExecution.Labels n 0)
    (hl : ∀ a : Fin 4, (StoredPartitionBlocks.block xs labels a).length = width n) :
    (run xs labels hl).2 ≤ 120 * (n + 1) ^ 2 := by
  have hw := CoordinateBlocksBuild.work (fun a => StoredPartitionBlocks.block xs labels a) hl
    (show width n ≤ n by unfold width RepresentationSetup.blockHalf; simp only [Matrix.cons_val_zero]; omega)
  have hm : PartitionLabelExecution.size n 0 ≤ n := by
    unfold PartitionLabelExecution.size RepresentationSetup.blockCount RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  change _ + 20 * PartitionLabelExecution.size n 0 + 9 ≤ _
  nlinarith only [hw, hm, Nat.zero_le (n ^ 2)]

end LowSpaceSubsetSum.StoredTopCoordinates

end OAI
