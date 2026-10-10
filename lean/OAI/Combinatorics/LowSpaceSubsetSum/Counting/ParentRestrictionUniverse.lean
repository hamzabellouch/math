import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentOverflow
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ParentPrefixSearch
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTopCounts
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationChosenStreams

namespace OAI

/-! # Early leaf restriction filters exactly the ambient entry universe -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationUniverse

variable {n : ℕ}

theorem leafTop_subset_topDomain (L : Fin 4 → RepresentationLeaf (Fin n)) (i : Fin 4) :
    (L i).top ⊆ topDomain L := by
  intro k hk
  fin_cases i <;> simp only [topDomain, Finset.mem_union] <;> tauto

theorem compatible_topSelections (L : Fin 4 → RepresentationLeaf (Fin n))
    (hd : ∀ i j, i ≠ j → Disjoint (L i).top (L j).top)
    {x : ParentOccurrence (Fin n)} (hx : x ∈ parents L)
    (P : MaskRestriction n) (hc : P.Compatible (topDomain L) (topMask x)) (i : Fin 4) :
    P.Compatible (L i).top (topSelections x i) := by
  rw [← topMask_inter_leaf L hd hx i]
  exact P.compatible_inter (leafTop_subset_topDomain L i) hc

end LowSpaceSubsetSum.RepresentationUniverse

namespace LowSpaceSubsetSum.MaskRestriction

variable {n : ℕ}

theorem force_compatible_iff (P : MaskRestriction n) (A S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ A) (side : Bool) :
    (P.force i side).Compatible A S ↔ P.Compatible A S ∧ decide (i ∈ S) = side := by
  cases side with
  | false =>
    simp only [force, Bool.false_eq_true, ↓reduceIte, Compatible,
      Finset.disjoint_insert_left, decide_eq_false_iff_not]
    tauto
  | true =>
    simp only [force, ↓reduceIte, Compatible, decide_eq_true_eq]
    constructor
    · rintro ⟨hones, hzeros⟩
      refine ⟨⟨?_, hzeros⟩, hones (Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hi⟩)⟩
      intro k hk
      obtain ⟨hkP, hkA⟩ := Finset.mem_inter.mp hk
      exact hones (Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hkP, hkA⟩)
    · rintro ⟨⟨hones, hzeros⟩, hiS⟩
      refine ⟨?_, hzeros⟩
      intro k hk
      obtain ⟨hkP, hkA⟩ := Finset.mem_inter.mp hk
      rcases Finset.mem_insert.mp hkP with rfl | hkP
      · exact hiS
      · exact hones (Finset.mem_inter.mpr ⟨hkP, hkA⟩)

end LowSpaceSubsetSum.MaskRestriction

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

theorem key_restriction (P : MaskRestriction n) (j : Fin 2) :
    ({ D with maskRestriction := P }).key j = D.key j := rfl

theorem rawEligible_restriction (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (x : Parent (n := n)) :
    ({ D with maskRestriction := P }).RawEligible x ↔
      ({ D with maskRestriction := MaskRestriction.empty }).RawEligible x ∧
        P.Compatible (RepresentationUniverse.topDomain D.leaves) (RepresentationUniverse.topMask x) := by
  let E := { D with maskRestriction := MaskRestriction.empty }
  let F := { D with maskRestriction := P }
  constructor
  · intro hx
    have hs0 := ((F.pair 0).output_mem x.1).mp hx.1
    have hs1 := ((F.pair 1).output_mem x.2).mp hx.2.1
    have he0 : x.1 ∈ (E.pair 0).output (E.pair 0).start := by
      apply ((E.pair 0).output_mem x.1).mpr
      exact ⟨⟨hs0.1.1, (MaskRestriction.empty.accept_eq_true (D.leaves 0).top x.1.1.1.1).mpr
        (MaskRestriction.empty_compatible _ _)⟩,
        ⟨hs0.2.1.1, (MaskRestriction.empty.accept_eq_true (D.leaves 1).top x.1.2.1.1).mpr
          (MaskRestriction.empty_compatible _ _)⟩, hs0.2.2⟩
    have he1 : x.2 ∈ (E.pair 1).output (E.pair 1).start := by
      apply ((E.pair 1).output_mem x.2).mpr
      exact ⟨⟨hs1.1.1, (MaskRestriction.empty.accept_eq_true (D.leaves 2).top x.2.1.1.1).mpr
        (MaskRestriction.empty_compatible _ _)⟩,
        ⟨hs1.2.1.1, (MaskRestriction.empty.accept_eq_true (D.leaves 3).top x.2.2.1.1).mpr
          (MaskRestriction.empty_compatible _ _)⟩, hs1.2.2⟩
    exact ⟨⟨he0, he1, hx.2.2.1, hx.2.2.2⟩,
      F.streams_compatible x.1 x.2 hx.1 hx.2.1⟩
  · rintro ⟨hx, hc⟩
    have hm := E.streams_parent x.1 x.2 hx.1 hx.2.1
    have hl := fun i => RepresentationUniverse.compatible_topSelections D.leaves hd hm P hc i
    have hs0 := ((E.pair 0).output_mem x.1).mp hx.1
    have hs1 := ((E.pair 1).output_mem x.2).mp hx.2.1
    exact F.rawEligible_of_filters x hm hx.2.2.2 (hl 0) (hl 1) (hl 2) (hl 3)
      hs0.2.2 hs1.2.2 (E.rawEligible_parent_mod x hx)

theorem entryUniverse_restriction (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top) :
    ({ D with maskRestriction := P }).entryUniverse =
      ({ D with maskRestriction := MaskRestriction.empty }).entryUniverse.filter
        (fun e => P.Compatible (RepresentationUniverse.topDomain D.leaves) e.mask) := by
  classical
  ext e
  simp only [entryUniverse, List.mem_toFinset, Finset.mem_filter, rawEntries_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, hc⟩ := (D.rawEligible_restriction P hd x).mp hx
    exact ⟨⟨x, hx, rfl⟩, hc⟩
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    exact ⟨x, (D.rawEligible_restriction P hd x).mpr ⟨hx, hc⟩, rfl⟩

theorem entryUniverse_force (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (i : Fin n) (hi : i ∈ RepresentationUniverse.topDomain D.leaves) (side : Bool) :
    ({ D with maskRestriction := P.force i side }).entryUniverse =
      ({ D with maskRestriction := P }).entryUniverse.filter (fun e => decide (i ∈ e.mask) = side) := by
  classical
  have hf := D.entryUniverse_restriction (P.force i side) hd
  have hp := D.entryUniverse_restriction P hd
  generalize ({ D with maskRestriction := MaskRestriction.empty }).entryUniverse = U at hf hp
  generalize ({ D with maskRestriction := P }).entryUniverse = V at hp ⊢
  generalize ({ D with maskRestriction := P.force i side }).entryUniverse = W at hf ⊢
  rw [hf, hp]
  ext e
  simp only [Finset.mem_filter, P.force_compatible_iff _ _ i hi side]
  tauto

end LowSpaceSubsetSum.RepresentationParentData

end

end OAI
