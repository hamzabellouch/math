import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParentStream
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.TopCoordinatesBlocks

namespace OAI

/-! # The prescribed local counts of every retained top mask -/

namespace LowSpaceSubsetSum.RepresentationUniverse

variable {n : ℕ}

def topSelections (x : ParentOccurrence (Fin n)) : Fin 4 → Finset (Fin n) :=
  ![x.1.1.1.1, x.1.2.1.1, x.2.1.1.1, x.2.2.1.1]

theorem topMask_eq_biUnion (x : ParentOccurrence (Fin n)) :
    topMask x = Finset.univ.biUnion (topSelections x) := by
  ext i
  simp [topMask, topSelections, Fin.exists_fin_succ]

theorem topSelections_spec (L : Fin 4 → RepresentationLeaf (Fin n))
    {x : ParentOccurrence (Fin n)} (hx : x ∈ parents L) (i : Fin 4) :
    topSelections x i ⊆ (L i).top ∧ (topSelections x i).card = (L i).topCount := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_parents L x).mp hx
  have h0 := Finset.mem_powersetCard.mp
    (Finset.mem_product.mp (Finset.mem_product.mp h0).1).1
  have h1 := Finset.mem_powersetCard.mp
    (Finset.mem_product.mp (Finset.mem_product.mp h1).1).1
  have h2 := Finset.mem_powersetCard.mp
    (Finset.mem_product.mp (Finset.mem_product.mp h2).1).1
  have h3 := Finset.mem_powersetCard.mp
    (Finset.mem_product.mp (Finset.mem_product.mp h3).1).1
  fin_cases i <;> assumption

theorem topMask_inter_leaf (L : Fin 4 → RepresentationLeaf (Fin n))
    (hd : ∀ i j, i ≠ j → Disjoint (L i).top (L j).top)
    {x : ParentOccurrence (Fin n)} (hx : x ∈ parents L) (i : Fin 4) :
    topMask x ∩ (L i).top = topSelections x i := by
  rw [topMask_eq_biUnion]
  ext k
  constructor
  · intro hk
    obtain ⟨hunion, hi⟩ := Finset.mem_inter.mp hk
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hunion
    by_cases hji : j = i
    · simpa only [hji] using hj
    · exact False.elim (Finset.disjoint_left.mp (hd j i hji)
        ((topSelections_spec L hx j).1 hj) hi)
  · intro hk
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hk⟩,
      (topSelections_spec L hx i).1 hk⟩

theorem topMask_inter_leaf_card (L : Fin 4 → RepresentationLeaf (Fin n))
    (hd : ∀ i j, i ≠ j → Disjoint (L i).top (L j).top)
    {x : ParentOccurrence (Fin n)} (hx : x ∈ parents L) (i : Fin 4) :
    (topMask x ∩ (L i).top).card = (L i).topCount := by
  rw [topMask_inter_leaf L hd hx i]
  exact (topSelections_spec L hx i).2

end LowSpaceSubsetSum.RepresentationUniverse

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n g : ℕ} (D : RepresentationParentData n)

theorem entries_local_count (B : ℕ) (blocks : Fin 4 → Finset (Fin n))
    (hc : ∀ i, (blocks i).card = g)
    (hd : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (ht : ∀ i, (D.leaves i).top = blocks i)
    (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) (i : Fin 4) :
    (SeparatorCheck.localMask i
      ((TopCoordinates.ofBlocks blocks hc hd).encodeEntry e).mask).card =
        (D.leaves i).topCount := by
  obtain ⟨x, hx, _, rfl, _⟩ := D.entries_provenance B e he
  rw [TopCoordinates.encodeEntry, RepresentationUniverse.entry,
    TopCoordinates.ofBlocks_local_card, ← ht i]
  exact RepresentationUniverse.topMask_inter_leaf_card D.leaves
    (fun j k hjk => by rw [ht j, ht k]; exact hd j k hjk) hx i

end LowSpaceSubsetSum.RepresentationParentData

end OAI
