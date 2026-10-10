import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ListSetCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionBlockCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredLeafPreparation

namespace OAI

/-! # Constructing all eight finite leaf profiles from stored lists

The three sets in a profile are built by the explicit tail insertion loop.
All eight completed profiles are cached before returning the index view.
-/

namespace LowSpaceSubsetSum.StoredLeafCells

open scoped BigOperators
variable {n : ℕ}

def leaf (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (side : Fin 2) (i : Fin 4) : (RepresentationLeaf (Fin n) × ℕ) × ℕ :=
  let top := PartitionBlockCells.run (domains 0) (labels 0) i
  let localPart := PartitionBlockCells.run (domains side.succ) (labels side.succ)
    ⟨i.val%2, by
      have h : RepresentationSetup.blockCount side.succ = 2 := by fin_cases side <;> rfl
      rw [h]
      exact Nat.mod_lt _ (by decide)⟩
  let bg := background[4*side.val+i.val]
  let t := ListSetCells.run top.1.1
  let m := ListSetCells.run localPart.1.1
  let b := ListSetCells.run bg
  (({ top := t.1.1
      mixer := m.1.1
      background := b.1.1
      topCount := if side = 0 then balancedBlockCounts 4 guesses[0] i
        else RepresentationSetup.blockHalf n 0-balancedBlockCounts 4 guesses[0] i
      localCount := if i.val < 2 then
          balancedBlockCounts 2 guesses[side.val+1] ⟨i.val%2, Nat.mod_lt _ (by decide)⟩
        else RepresentationSetup.blockHalf n side.succ-
          balancedBlockCounts 2 guesses[side.val+1] ⟨i.val%2, Nat.mod_lt _ (by decide)⟩ },
    top.1.2+localPart.1.2+4*(top.1.1.length+localPart.1.1.length+bg.length+1)^2+20),
    top.2+localPart.2+t.2+m.2+b.2+4*(top.1.1.length+localPart.1.1.length+bg.length+1)+32)

theorem leaf_value (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3) (side : Fin 2) (i : Fin 4) :
    (leaf domains labels background guesses side i).1 =
      StoredLeafPreparation.leaf domains labels background guesses side i := by
  let a : Fin (RepresentationSetup.blockCount side.succ) := ⟨i.val%2, by
    have h : RepresentationSetup.blockCount side.succ = 2 := by fin_cases side <;> rfl
    rw [h]
    exact Nat.mod_lt _ (by decide)⟩
  have ht := PartitionBlockCells.value (domains 0) (labels 0) i
  have hm := PartitionBlockCells.value (domains side.succ) (labels side.succ) a
  have ht₁ := congrArg Prod.fst ht
  have ht₂ := congrArg Prod.snd ht
  have hm₁ := congrArg Prod.fst hm
  have hm₂ := congrArg Prod.snd hm
  dsimp only [a] at hm₁ hm₂
  simp only [leaf, ListSetCells.value, ht₁, ht₂, hm₁, hm₂,
    StoredLeafPreparation.leaf, StoredLeafPreparation.make]

private theorem size_le (j : Fin 3) : PartitionLabelExecution.size n j ≤ n := by
  fin_cases j <;> norm_num [PartitionLabelExecution.size, RepresentationSetup.blockCount,
    RepresentationSetup.blockHalf] <;> omega

theorem leaf_cells (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (hb : ∀ j : Fin 8, background[j.val].length ≤ n) (side : Fin 2) (i : Fin 4) :
    (leaf domains labels background guesses side i).2 ≤ 512*(n+1)^2 := by
  let a : Fin (RepresentationSetup.blockCount side.succ) := ⟨i.val%2, by
    have h : RepresentationSetup.blockCount side.succ = 2 := by fin_cases side <;> rfl
    rw [h]
    exact Nat.mod_lt _ (by decide)⟩
  have ht := PartitionBlockCells.cells (domains 0) (labels 0) i
  have hm := PartitionBlockCells.cells (domains side.succ) (labels side.succ) a
  have htl := (PartitionBlockCells.length (domains 0) (labels 0) i).trans (size_le (n := n) 0)
  have hml := (PartitionBlockCells.length (domains side.succ) (labels side.succ) a).trans
    (size_le (n := n) side.succ)
  have hbl := hb ⟨4*side.val+i.val, by omega⟩
  have hc₀ := ListSetCells.cells (PartitionBlockCells.run (domains 0) (labels 0) i).1.1
  have hc₁ := ListSetCells.cells (PartitionBlockCells.run (domains side.succ) (labels side.succ) a).1.1
  have hc₂ := ListSetCells.cells background[4*side.val+i.val]
  have hs₀ := size_le (n := n) 0
  have hs₁ := size_le (n := n) side.succ
  change _+_+_+_+_+_+32 ≤ _
  change (PartitionBlockCells.run (domains 0) (labels 0) i).2+
    (PartitionBlockCells.run (domains side.succ) (labels side.succ) a).2+_+_+_+_+32 ≤ _
  dsimp only at hbl
  nlinarith only [ht, hm, htl, hml, hbl, hc₀, hc₁, hc₂, hs₀, hs₁, Nat.zero_le (n^2)]

def run (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3) :
    ((Fin 2 → Fin 4 → RepresentationLeaf (Fin n)) × ℕ) × ℕ :=
  let rows := Vector.ofFn (fun side : Fin 2 => Vector.ofFn (fun i : Fin 4 =>
    leaf domains labels background guesses side i))
  ((fun side i => rows[side.val][i.val].1.1,
    (∑ side : Fin 2, ∑ i : Fin 4, rows[side.val][i.val].1.2)+8),
    (∑ side : Fin 2, ∑ i : Fin 4, rows[side.val][i.val].2)+16*(n+1))

theorem value (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3) :
    (run domains labels background guesses).1 = StoredLeafPreparation.run domains labels background guesses := by
  simp only [run, Vector.getElem_ofFn, Fin.eta, leaf_value, StoredLeafPreparation.run]

theorem cells (domains : StoredOrderedMixers.Domains n) (labels : StoredPartitions.Data n)
    (background : Vector (List (Fin n)) 8) (guesses : Vector ℕ 3)
    (hb : ∀ j : Fin 8, background[j.val].length ≤ n) :
    (run domains labels background guesses).2 ≤ 8192*(n+1)^2 := by
  have h := Finset.sum_le_sum (fun side (_ : side ∈ (Finset.univ : Finset (Fin 2))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      leaf_cells domains labels background guesses hb side i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  simp only [run, Vector.getElem_ofFn, Fin.eta]
  nlinarith only [h, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.StoredLeafCells

end OAI
