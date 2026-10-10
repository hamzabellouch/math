import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPartitions
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CoordinateBlocksBuild

namespace OAI

/-! # Extracting actual index lists from the stored balanced labels -/

namespace LowSpaceSubsetSum.StoredPartitionBlocks

variable {n m b : ℕ}

def domain (xs : List (Fin n)) (hm : xs.length = m) : Vector (Fin n) m :=
  ⟨xs.toArray, by simpa only [List.size_toArray] using hm⟩

theorem domain_source (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (j : Fin 3) (xs : List (Fin n)) (hm : xs.length = PartitionLabelExecution.size n j)
    (hx : xs = (R.orderedMixers z j).sort (· ≤ ·))
    (k : Fin (PartitionLabelExecution.size n j)) :
    (domain xs hm)[k.val] = ((CanonicalPartition.ranks R z j).symm k).val := by
  subst xs
  change ((R.orderedMixers z j).sort (· ≤ ·))[k.val] =
    ((R.orderedMixers z j).orderIsoOfFin (CanonicalPartition.size_eq R z j) k).val
  rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  rfl

def block (xs : Vector (Fin n) m) (labels : Vector (Fin b) m) (a : Fin b) : List (Fin n) :=
  ((List.finRange m).filter (fun k => decide (labels[k.val] = a))).map (fun k => xs[k.val])

theorem mem_block (xs : Vector (Fin n) m) (labels : Vector (Fin b) m)
    (a : Fin b) (x : Fin n) :
    x ∈ block xs labels a ↔ ∃ k : Fin m, labels[k.val] = a ∧ xs[k.val] = x := by
  simp only [block, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]

theorem nodup (xs : Vector (Fin n) m) (labels : Vector (Fin b) m)
    (a : Fin b) (hx : Function.Injective (fun k : Fin m => xs[k.val])) :
    (block xs labels a).Nodup :=
  ((List.nodup_finRange m).filter _).map hx

def run (xs : Vector (Fin n) m) (labels : Vector (Fin b) m) (a : Fin b) :
    List (Fin n) × ℕ := (block xs labels a, 5 * m + 1)

theorem source (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (f : R.Partitions z) (j : Fin 3)
    (xs : Vector (Fin n) (PartitionLabelExecution.size n j))
    (labels : PartitionArrayExecution.Labels n j)
    (hx : ∀ k, xs[k.val] = ((CanonicalPartition.ranks R z j).symm k).val)
    (hl : ∀ k, labels[k.val] = (f j).val ((CanonicalPartition.ranks R z j).symm k))
    (a : Fin (RepresentationSetup.blockCount j)) :
    (run xs labels a).1.toFinset = R.rawPartitionBlock z f j a.val := by
  classical
  ext x
  simp only [run, List.mem_toFinset, mem_block, RepresentationSetup.rawPartitionBlock,
    Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, he⟩
    have hxk := hx k
    have hmem : x ∈ R.orderedMixers z j := by
      rw [← he, hxk]
      exact ((CanonicalPartition.ranks R z j).symm k).property
    refine ⟨hmem, hmem, ?_⟩
    have hs : (⟨x, hmem⟩ : ↥(R.orderedMixers z j)) =
        (CanonicalPartition.ranks R z j).symm k := Subtype.ext (he.symm.trans hxk)
    rw [hs, ← hl k, hk]
  · rintro ⟨hmem, hmem', he⟩
    let k := CanonicalPartition.ranks R z j ⟨x, hmem⟩
    refine ⟨k, ?_, ?_⟩
    · rw [hl]
      change (f j).val ((CanonicalPartition.ranks R z j).symm
        (CanonicalPartition.ranks R z j ⟨x, hmem⟩)) = a
      rw [Equiv.symm_apply_apply]
      apply Fin.ext
      exact he
    · rw [hx]
      exact congrArg Subtype.val ((CanonicalPartition.ranks R z j).symm_apply_apply ⟨x, hmem⟩)

theorem length_source (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (f : R.Partitions z) (j : Fin 3)
    (xs : Vector (Fin n) (PartitionLabelExecution.size n j))
    (labels : PartitionArrayExecution.Labels n j)
    (hx : ∀ k, xs[k.val] = ((CanonicalPartition.ranks R z j).symm k).val)
    (hl : ∀ k, labels[k.val] = (f j).val ((CanonicalPartition.ranks R z j).symm k))
    (a : Fin (RepresentationSetup.blockCount j)) :
    (run xs labels a).1.length = 2 * RepresentationSetup.blockHalf n j := by
  have hi : Function.Injective (fun k : Fin (PartitionLabelExecution.size n j) => xs[k.val]) := by
    intro k l h
    apply (CanonicalPartition.ranks R z j).symm.injective
    apply Subtype.ext
    simpa only [← hx] using h
  have hnodup := nodup xs labels a hi
  have hcard := R.rawPartitionBlock_card z f j a
  rw [← source R z f j xs labels hx hl a] at hcard
  simpa only [run, List.toFinset_card_of_nodup hnodup] using hcard

end LowSpaceSubsetSum.StoredPartitionBlocks

end OAI
