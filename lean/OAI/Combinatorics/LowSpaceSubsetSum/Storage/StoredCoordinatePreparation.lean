import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredTopCoordinates
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredOrderedMixers

namespace OAI

/-! # Guarded coordinate construction from the stored top-domain labels -/

namespace LowSpaceSubsetSum.StoredCoordinatePreparation

variable {n : ℕ}

abbrev Rows (n : ℕ) := Fin 4 → Vector (Fin n) (StoredTopCoordinates.width n)

def run (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n) :
    Option (Rows n) × ℕ :=
  if h : ∀ a : Fin 4, (StoredPartitionBlocks.block (domains 0) (labels 0) a).length =
      StoredTopCoordinates.width n then
    let out := StoredTopCoordinates.run (domains 0) (labels 0) h
    (some out.1, out.2 + 20 * PartitionLabelExecution.size n 0 + 8)
  else (none, 20 * PartitionLabelExecution.size n 0 + 8)

theorem complete (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (f : R.Partitions z) (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (hd : ∀ k, (domains 0)[k.val] = ((CanonicalPartition.ranks R z 0).symm k).val)
    (hl : ∀ k, (labels 0)[k.val] = (f 0).val ((CanonicalPartition.ranks R z 0).symm k)) :
    ∃ rows, (run domains labels).1 = some rows ∧
      ∀ (a : Fin 4) (k : Fin (StoredTopCoordinates.width n)),
        (rows a)[k.val] = (R.topCoordinates z f).index (a, k) := by
  have hs (a : Fin 4) : (StoredPartitionBlocks.block (domains 0) (labels 0) a).length =
      StoredTopCoordinates.width n :=
    StoredPartitionBlocks.length_source R z f 0 (domains 0) (labels 0) hd hl a
  refine ⟨(StoredTopCoordinates.run (domains 0) (labels 0) hs).1, ?_, ?_⟩
  · simp only [run, dite_eq_left hs]
  · exact StoredTopCoordinates.value R z f (domains 0) (labels 0) hd hl hs

theorem work (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n) :
    (run domains labels).2 ≤ 150 * (n + 1) ^ 2 := by
  have hm : PartitionLabelExecution.size n 0 ≤ n := by
    unfold PartitionLabelExecution.size RepresentationSetup.blockCount RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  unfold run
  split
  next h =>
    have hw := StoredTopCoordinates.work (domains 0) (labels 0) h
    change _ + 20 * PartitionLabelExecution.size n 0 + 8 ≤ _
    nlinarith only [hm, hw, Nat.zero_le (n ^ 2)]
  · nlinarith only [hm, Nat.zero_le (n ^ 2)]

end LowSpaceSubsetSum.StoredCoordinatePreparation

end OAI
