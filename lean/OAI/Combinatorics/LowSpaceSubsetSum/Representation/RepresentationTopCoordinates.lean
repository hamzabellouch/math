import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTopCounts
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafDomains

namespace OAI

/-! # The concrete representation layout in the separator's coordinates -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def topCoordinates (z : Layout n) (f : R.Partitions z) :
    TopCoordinates n (2 * blockHalf n 0) :=
  TopCoordinates.ofBlocks (fun i : Fin 4 => R.rawPartitionBlock z f 0 i.val)
    (fun i => R.rawPartitionBlock_card z f 0 i)
    (fun _i _j hij => R.rawPartitionBlock_disjoint z f 0 (fun he => hij (Fin.ext he)))

theorem topCoordinates_domain (z : Layout n) (f : R.Partitions z) :
    (R.topCoordinates z f).domain = R.orderedMixers z 0 := by
  rw [topCoordinates, TopCoordinates.ofBlocks_domain]
  exact R.rawPartitionBlock_biUnion z f 0

theorem rawEntry_local_count (z : Layout n) (guesses : Guesses n) (f : R.Partitions z)
    (background : Fin n → Fin 2 × Fin 4) (side : Fin 2)
    (a : Fin n → ℤ) (e : Entry (Fin n))
    (he : e ∈ RepresentationUniverse.validEntries a (R.rawLeaf z guesses f background side))
    (i : Fin 4) :
    (SeparatorCheck.localMask i ((R.topCoordinates z f).encodeEntry e).mask).card =
      if side = 0 then balancedBlockCounts 4 (guesses 0).val i
      else blockHalf n 0 - balancedBlockCounts 4 (guesses 0).val i := by
  classical
  simp only [RepresentationUniverse.validEntries, Finset.mem_image, Finset.mem_filter] at he
  obtain ⟨x, ⟨hx, _⟩, rfl⟩ := he
  rw [TopCoordinates.encodeEntry, RepresentationUniverse.entry, topCoordinates,
    TopCoordinates.ofBlocks_local_card]
  exact RepresentationUniverse.topMask_inter_leaf_card
    (R.rawLeaf z guesses f background side)
    (fun j k hjk => R.rawPartitionBlock_disjoint z f 0 (fun he => hjk (Fin.ext he))) hx i

theorem collected_local_count (z : Layout n) (guesses : Guesses n) (f : R.Partitions z)
    (background : Fin n → Fin 2 × Fin 4) (side : Fin 2)
    (D : RepresentationParentData n) (hleaves : D.leaves = R.rawLeaf z guesses f background side)
    (B : ℕ) (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) (i : Fin 4) :
    (SeparatorCheck.localMask i ((R.topCoordinates z f).encodeEntry e).mask).card =
      if side = 0 then balancedBlockCounts 4 (guesses 0).val i
      else blockHalf n 0 - balancedBlockCounts 4 (guesses 0).val i := by
  have h := D.entries_local_count B
    (fun i : Fin 4 => R.rawPartitionBlock z f 0 i.val)
    (fun i => R.rawPartitionBlock_card z f 0 i)
    (fun _i _j hij => R.rawPartitionBlock_disjoint z f 0 (fun he => hij (Fin.ext he)))
    (fun i => by rw [hleaves]; rfl) e he i
  rw [hleaves] at h
  exact h

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
