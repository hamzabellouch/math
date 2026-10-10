import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredOrderedMixers
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBackgroundSource

namespace OAI

/-! # The eight leaf profiles computed from stored index lists

Both prescribed subset sizes use integer division of the stored guesses.
The domains are obtained by scanning the stored labels and by reading the
eight consecutive background rows.
-/

namespace LowSpaceSubsetSum.StoredLeafPreparation

open scoped BigOperators
variable {n : ℕ}

def make (top mixer background : List (Fin n)) (guesses : Vector ℕ 3)
    (side : Fin 2) (leaf : Fin 4) : RepresentationLeaf (Fin n) where
  top := top.toFinset
  mixer := mixer.toFinset
  background := background.toFinset
  topCount := if side = 0 then balancedBlockCounts 4 guesses[0] leaf
    else RepresentationSetup.blockHalf n 0 - balancedBlockCounts 4 guesses[0] leaf
  localCount := if leaf.val < 2 then
      balancedBlockCounts 2 guesses[side.val + 1] ⟨leaf.val % 2, Nat.mod_lt _ (by decide)⟩
    else RepresentationSetup.blockHalf n side.succ -
      balancedBlockCounts 2 guesses[side.val + 1] ⟨leaf.val % 2, Nat.mod_lt _ (by decide)⟩

def leaf (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (side : Fin 2) (i : Fin 4) : RepresentationLeaf (Fin n) × ℕ :=
  let top := StoredPartitionBlocks.run (domains 0) (labels 0) i
  let mixer := StoredPartitionBlocks.run (domains side.succ) (labels side.succ)
    ⟨i.val % 2, by
      have : RepresentationSetup.blockCount side.succ = 2 := by fin_cases side <;> rfl
      rw [this]
      exact Nat.mod_lt _ (by decide)⟩
  let bg := background[4 * side.val + i.val]
  (make top.1 mixer.1 bg guesses side i,
    top.2 + mixer.2 + 4 * (top.1.length + mixer.1.length + bg.length + 1) ^ 2 + 20)

def run (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3) :
    (Fin 2 → Fin 4 → RepresentationLeaf (Fin n)) × ℕ :=
  (fun side i => (leaf domains labels background guesses side i).1,
    (∑ side : Fin 2, ∑ i : Fin 4, (leaf domains labels background guesses side i).2) + 8)

theorem value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (g : RepresentationSetup.Guesses n) (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4)
    (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (hd : ∀ (j : Fin 3) (k : Fin (PartitionLabelExecution.size n j)),
      (domains j)[k.val] = ((CanonicalPartition.ranks R z j).symm k).val)
    (hl : ∀ (j : Fin 3) (k : Fin (PartitionLabelExecution.size n j)),
      (labels j)[k.val] = (f j).val ((CanonicalPartition.ranks R z j).symm k))
    (hb : ∀ (side : Fin 2) (i : Fin 4),
      background[4 * side.val + i.val].toFinset = R.rawBackground z B side i)
    (hg : ∀ j : Fin 3, guesses[j.val] = (g j).val)
    (side : Fin 2) (i : Fin 4) :
    (run domains labels background guesses).1 side i = R.rawLeaf z g f B side i := by
  have ht := StoredPartitionBlocks.source R z f 0 (domains 0) (labels 0) (hd 0) (hl 0) i
  let a : Fin (RepresentationSetup.blockCount side.succ) := ⟨i.val % 2, by
    have : RepresentationSetup.blockCount side.succ = 2 := by fin_cases side <;> rfl
    rw [this]
    exact Nat.mod_lt _ (by decide)⟩
  have hm := StoredPartitionBlocks.source R z f side.succ (domains side.succ)
    (labels side.succ) (hd side.succ) (hl side.succ) a
  dsimp only [a] at hm
  have h0 := hg 0
  have hside := hg side.succ
  dsimp only [Fin.val_zero, Fin.val_succ] at h0 hside
  simp only [run, leaf, make, ht, hm, hb, h0, hside, RepresentationSetup.rawLeaf]

theorem block_length_le {m b : ℕ} (xs : Vector (Fin n) m) (labels : Vector (Fin b) m)
    (a : Fin b) : (StoredPartitionBlocks.run xs labels a).1.length ≤ m := by
  change ((List.finRange m).filter _ |>.map _).length ≤ m
  simpa only [List.length_map, List.length_finRange] using List.length_filter_le _ (List.finRange m)

theorem leaf_work (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (hb : ∀ j : Fin 8, background[j.val].length ≤ n) (side : Fin 2) (i : Fin 4) :
    (leaf domains labels background guesses side i).2 ≤ 100 * (n + 1) ^ 2 := by
  have hs (j : Fin 3) : PartitionLabelExecution.size n j ≤ n := by
    fin_cases j <;>
      norm_num [PartitionLabelExecution.size, RepresentationSetup.blockCount,
        RepresentationSetup.blockHalf] <;> omega
  have ht := block_length_le (domains 0) (labels 0) i
  let a : Fin (RepresentationSetup.blockCount side.succ) := ⟨i.val % 2, by
    have : RepresentationSetup.blockCount side.succ = 2 := by fin_cases side <;> rfl
    rw [this]
    exact Nat.mod_lt _ (by decide)⟩
  have hm := block_length_le (domains side.succ) (labels side.succ) a
  have hbg := hb ⟨4 * side.val + i.val, by omega⟩
  dsimp only at hbg
  have hs0 := hs 0
  have hss := hs side.succ
  have ht' : (StoredPartitionBlocks.run (domains 0) (labels 0) i).1.length ≤ n := ht.trans hs0
  have hm' : (StoredPartitionBlocks.run (domains side.succ) (labels side.succ) a).1.length ≤ n := hm.trans hss
  have hsum : (StoredPartitionBlocks.run (domains 0) (labels 0) i).1.length +
      (StoredPartitionBlocks.run (domains side.succ) (labels side.succ) a).1.length +
        background[4 * side.val + i.val].length + 1 ≤ 3 * n + 1 := by omega
  have hsq := Nat.pow_le_pow_left hsum 2
  change 5 * PartitionLabelExecution.size n 0 + 1 +
    (5 * PartitionLabelExecution.size n side.succ + 1) + 4 *
      ((StoredPartitionBlocks.run (domains 0) (labels 0) i).1.length +
       (StoredPartitionBlocks.run (domains side.succ) (labels side.succ) a).1.length +
       background[4 * side.val + i.val].length + 1) ^ 2 + 20 ≤ _
  nlinarith only [hs0, hss, hsq, Nat.zero_le (n ^ 2)]

theorem work (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (hb : ∀ j : Fin 8, background[j.val].length ≤ n) :
    (run domains labels background guesses).2 ≤ 1000 * (n + 1) ^ 2 := by
  have hs := Finset.sum_le_sum (fun side (_ : side ∈ (Finset.univ : Finset (Fin 2))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      leaf_work domains labels background guesses hb side i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  change (∑ side : Fin 2, ∑ i : Fin 4, (leaf domains labels background guesses side i).2) + 8 ≤ _
  nlinarith only [hs, Nat.one_le_pow 2 (n + 1) (by omega : 1 ≤ n + 1)]

end LowSpaceSubsetSum.StoredLeafPreparation

end OAI
