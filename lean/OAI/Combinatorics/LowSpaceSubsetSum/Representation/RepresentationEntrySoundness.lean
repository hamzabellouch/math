import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParentStream

namespace OAI

/-! # Original indexed subset witnesses for retained parent entries -/

namespace LowSpaceSubsetSum

namespace RepresentationUniverse

variable {n : ℕ}

def parentDomain (L : Fin 4 → RepresentationLeaf (Fin n)) : Finset (Fin n) :=
  (topDomain L ∪ mixerDomain L) ∪ backgroundDomain L

theorem entry_represents (a : Fin n → ℤ) (L : Fin 4 → RepresentationLeaf (Fin n))
    (htl : Disjoint (topDomain L) (mixerDomain L))
    (htb : Disjoint (topDomain L) (backgroundDomain L))
    (hlb : Disjoint (mixerDomain L) (backgroundDomain L))
    {x : ParentOccurrence (Fin n)} (hx : x ∈ parents L) (hv : Valid x) :
    Represents a (parentDomain L) (topDomain L) (entry a x) := by
  obtain ⟨ht, hl, hb⟩ := parent_part_subsets L hx
  have dtl := htl.mono ht hl
  have dtb := htb.mono ht hb
  have dlb := hlb.mono hl hb
  refine ⟨(topMask x ∪ localMask x) ∪ backgroundMask x,
    Finset.union_subset_union (Finset.union_subset_union ht hl) hb, ?_, ?_⟩
  · rw [weight_union a (Finset.disjoint_union_left.mpr ⟨dtb, dlb⟩), weight_union a dtl]
    exact (valid_weight a hv).symm
  · ext i
    constructor
    · intro hi
      obtain ⟨hi, hiTop⟩ := Finset.mem_inter.mp hi
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_union.mp hi with hi | hi
        · exact hi
        · exact (Finset.disjoint_left.mp htl hiTop (hl hi)).elim
      · exact (Finset.disjoint_left.mp htb hiTop (hb hi)).elim
    · intro hi
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hi), ht hi⟩

end RepresentationUniverse

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

theorem entry_represents (B : ℕ)
    (htl : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.mixerDomain D.leaves))
    (htb : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (hlb : Disjoint (RepresentationUniverse.mixerDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) :
    Represents D.weights (RepresentationUniverse.parentDomain D.leaves)
      (RepresentationUniverse.topDomain D.leaves) e := by
  obtain ⟨x, hx, hv, rfl, _⟩ := D.entries_provenance B e he
  exact RepresentationUniverse.entry_represents D.weights D.leaves htl htb hlb hx hv

theorem entry_bounded (B : ℕ)
    (htl : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.mixerDomain D.leaves))
    (htb : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (hlb : Disjoint (RepresentationUniverse.mixerDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) :
    WeightEncoding.BoundedWeight D.input e.value := by
  obtain ⟨S, _, hw, _⟩ := D.entry_represents B htl htb hlb e he
  rw [← hw]
  exact WeightEncoding.signed_weight_bounded D.input D.signs S

end RepresentationParentData
end LowSpaceSubsetSum

end OAI
