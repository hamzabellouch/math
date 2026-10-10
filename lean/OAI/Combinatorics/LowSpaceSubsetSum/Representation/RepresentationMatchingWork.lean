import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStreamWork
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixTaskCount

namespace OAI

/-! # Raw matching-occurrence charges through the executable prefix tree

Invalid tuples are included: the join must report them before the callback
can reject them. Early prefix filtering partitions this larger universe too.
-/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

theorem matchingUniverse_mem (x : Parent (n := n)) :
    x ∈ D.matchingUniverse ↔
      x.1 ∈ (D.pair 0).output (D.pair 0).start ∧
        x.2 ∈ (D.pair 1).output (D.pair 1).start ∧ D.key 0 x.1 = D.key 1 x.2 := by
  classical
  simp only [matchingUniverse, Finset.mem_filter, Finset.mem_product,
    ← (D.pair 0).output_toFinset, ← (D.pair 1).output_toFinset, List.mem_toFinset]
  tauto

theorem matching_restriction (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (x : Parent (n := n)) :
    x ∈ ({ D with maskRestriction := P }).matchingUniverse ↔
      x ∈ ({ D with maskRestriction := MaskRestriction.empty }).matchingUniverse ∧
        P.Compatible (RepresentationUniverse.topDomain D.leaves)
          (RepresentationUniverse.topMask x) := by
  let E := { D with maskRestriction := MaskRestriction.empty }
  let F := { D with maskRestriction := P }
  rw [F.matchingUniverse_mem, E.matchingUniverse_mem]
  constructor
  · rintro ⟨hx, hy, hk⟩
    have hs0 := ((F.pair 0).output_mem x.1).mp hx
    have hs1 := ((F.pair 1).output_mem x.2).mp hy
    have he0 : x.1 ∈ (E.pair 0).output (E.pair 0).start := by
      apply ((E.pair 0).output_mem x.1).mpr
      exact ⟨⟨hs0.1.1,
        (MaskRestriction.empty.accept_eq_true (D.leaves 0).top x.1.1.1.1).mpr
          (MaskRestriction.empty_compatible _ _)⟩,
        ⟨hs0.2.1.1,
          (MaskRestriction.empty.accept_eq_true (D.leaves 1).top x.1.2.1.1).mpr
            (MaskRestriction.empty_compatible _ _)⟩, hs0.2.2⟩
    have he1 : x.2 ∈ (E.pair 1).output (E.pair 1).start := by
      apply ((E.pair 1).output_mem x.2).mpr
      exact ⟨⟨hs1.1.1,
        (MaskRestriction.empty.accept_eq_true (D.leaves 2).top x.2.1.1.1).mpr
          (MaskRestriction.empty_compatible _ _)⟩,
        ⟨hs1.2.1.1,
          (MaskRestriction.empty.accept_eq_true (D.leaves 3).top x.2.2.1.1).mpr
            (MaskRestriction.empty_compatible _ _)⟩, hs1.2.2⟩
    exact ⟨⟨he0, he1, hk⟩, F.streams_compatible x.1 x.2 hx hy⟩
  · rintro ⟨⟨hx, hy, hk⟩, hc⟩
    have hm := E.streams_parent x.1 x.2 hx hy
    have hl := fun i => RepresentationUniverse.compatible_topSelections D.leaves hd hm P hc i
    have hs0 := ((E.pair 0).output_mem x.1).mp hx
    have hs1 := ((E.pair 1).output_mem x.2).mp hy
    refine ⟨((F.pair 0).output_mem x.1).mpr ?_, ((F.pair 1).output_mem x.2).mpr ?_, hk⟩
    · exact ⟨⟨hs0.1.1, (P.accept_eq_true _ _).mpr (hl 0)⟩,
        ⟨hs0.2.1.1, (P.accept_eq_true _ _).mpr (hl 1)⟩, hs0.2.2⟩
    · exact ⟨⟨hs1.1.1, (P.accept_eq_true _ _).mpr (hl 2)⟩,
        ⟨hs1.2.1.1, (P.accept_eq_true _ _).mpr (hl 3)⟩, hs1.2.2⟩

theorem matchingUniverse_restriction (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top) :
    ({ D with maskRestriction := P }).matchingUniverse =
      ({ D with maskRestriction := MaskRestriction.empty }).matchingUniverse.filter
        (fun x => P.Compatible (RepresentationUniverse.topDomain D.leaves)
          (RepresentationUniverse.topMask x)) := by
  classical
  ext x
  constructor
  · intro hx
    apply Finset.mem_filter.mpr
    exact (D.matching_restriction P hd x).mp hx
  · intro hx
    exact (D.matching_restriction P hd x).mpr (Finset.mem_filter.mp hx)

theorem matchingUniverse_force (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (i : Fin n) (hi : i ∈ RepresentationUniverse.topDomain D.leaves) (side : Bool) :
    ({ D with maskRestriction := P.force i side }).matchingUniverse =
      ({ D with maskRestriction := P }).matchingUniverse.filter
        (fun x => decide (i ∈ RepresentationUniverse.topMask x) = side) := by
  classical
  have hf := D.matchingUniverse_restriction (P.force i side) hd
  have hp := D.matchingUniverse_restriction P hd
  generalize ({ D with maskRestriction := MaskRestriction.empty }).matchingUniverse = U at hf hp
  generalize ({ D with maskRestriction := P }).matchingUniverse = V at hp ⊢
  generalize ({ D with maskRestriction := P.force i side }).matchingUniverse = W at hf ⊢
  rw [hf, hp]
  ext x
  simp only [Finset.mem_filter, P.force_compatible_iff _ _ i hi side]
  tauto

theorem matchingUniverse_force_card_add (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (i : Fin n) (hi : i ∈ RepresentationUniverse.topDomain D.leaves) :
    ({ D with maskRestriction := P.force i false }).matchingUniverse.card +
      ({ D with maskRestriction := P.force i true }).matchingUniverse.card =
        ({ D with maskRestriction := P }).matchingUniverse.card := by
  classical
  rw [D.matchingUniverse_force P hd i hi false, D.matchingUniverse_force P hd i hi true]
  have h := Finset.card_filter_add_card_filter_not
    (s := ({ D with maskRestriction := P }).matchingUniverse)
    (p := fun x => i ∈ RepresentationUniverse.topMask x)
  simpa only [decide_eq_false_iff_not, decide_eq_true_eq, add_comm] using h

/-- A proof view of all matching occurrences visited if YES checks are
ignored. The runtime does not build this tree or its list of occurrences. -/
def matchingVisits (B : ℕ) : List (Fin n) → MaskRestriction n → ℕ
  | [], P => ({ D with maskRestriction := P }).matchingUniverse.card
  | i :: order, P =>
    ({ D with maskRestriction := P }).matchingUniverse.card +
      if ({ D with maskRestriction := P }.collect B).state.user.keys.overflow then
        matchingVisits B order (P.force i false) + matchingVisits B order (P.force i true)
      else 0

theorem matchingVisits_le (B : ℕ)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (order : List (Fin n))
    (horder : ∀ i ∈ order, i ∈ RepresentationUniverse.topDomain D.leaves)
    (P : MaskRestriction n) :
    D.matchingVisits B order P ≤
      (order.length + 1) * ({ D with maskRestriction := P }).matchingUniverse.card := by
  induction order generalizing P with
  | nil => simp [matchingVisits]
  | cons i order ih =>
    simp only [matchingVisits, List.length_cons]
    split
    · have h0 := ih (fun j hj => horder j (by simp [hj])) (P.force i false)
      have h1 := ih (fun j hj => horder j (by simp [hj])) (P.force i true)
      have hs := D.matchingUniverse_force_card_add P hd i (horder i (by simp))
      generalize ({ D with maskRestriction := P }).matchingUniverse.card = U at hs ⊢
      generalize ({ D with maskRestriction := P.force i false }).matchingUniverse.card = U0 at h0 hs
      generalize ({ D with maskRestriction := P.force i true }).matchingUniverse.card = U1 at h1 hs
      nlinarith only [h0, h1, hs]
    · simp only [Nat.add_zero]
      exact Nat.le_mul_of_pos_left _ (by omega)

/-- Early leaf restrictions only remove child stream occurrences. -/
theorem pair_outputUniverse_subset_unrestricted (P : MaskRestriction n) (j : Fin 2) :
    ({ D with maskRestriction := P }.pair j).outputUniverse ⊆
      ({ D with maskRestriction := MaskRestriction.empty }.pair j).outputUniverse := by
  let E := { D with maskRestriction := MaskRestriction.empty }
  let F := { D with maskRestriction := P }
  intro x hx
  have hs := ((F.pair j).output_mem x).mp
    (List.mem_toFinset.mp ((F.pair j).output_toFinset ▸ hx))
  rw [← (E.pair j).output_toFinset]
  apply List.mem_toFinset.mpr
  apply ((E.pair j).output_mem x).mpr
  refine ⟨⟨hs.1.1, ?_⟩, ⟨hs.2.1.1, ?_⟩, hs.2.2⟩
  · exact (MaskRestriction.empty.accept_eq_true
      (D.leaves ⟨2 * j.val, by omega⟩).top x.1.1.1).mpr
      (MaskRestriction.empty_compatible _ _)
  · exact (MaskRestriction.empty.accept_eq_true
      (D.leaves ⟨2 * j.val + 1, by omega⟩).top x.2.1.1).mpr
      (MaskRestriction.empty_compatible _ _)

def unrestrictedChildCount : ℕ :=
  ({ D with maskRestriction := MaskRestriction.empty }.pair 0).outputUniverse.card +
    ({ D with maskRestriction := MaskRestriction.empty }.pair 1).outputUniverse.card

theorem restricted_collect_queries_le (B : ℕ) (P : MaskRestriction n) :
    ({ D with maskRestriction := P }.collect B).state.queries ≤
      6 * D.unrestrictedChildCount +
        ({ D with maskRestriction := P }).matchingUniverse.card + 2 := by
  have h0 := Finset.card_le_card (D.pair_outputUniverse_subset_unrestricted P 0)
  have h1 := Finset.card_le_card (D.pair_outputUniverse_subset_unrestricted P 1)
  have hq := ({ D with maskRestriction := P }).collect_query_bounds B
  dsimp only at hq
  unfold unrestrictedChildCount
  omega

/-- Actual reader calls summed over the hypothetical full prefix execution. -/
def queryVisits (B : ℕ) : List (Fin n) → MaskRestriction n → ℕ
  | [], P => ({ D with maskRestriction := P }.collect B).state.queries
  | i :: order, P =>
    ({ D with maskRestriction := P }.collect B).state.queries +
      if ({ D with maskRestriction := P }.collect B).state.user.keys.overflow then
        queryVisits B order (P.force i false) + queryVisits B order (P.force i true)
      else 0

theorem queryVisits_le_tasks_matching (B : ℕ) (order : List (Fin n)) (P : MaskRestriction n) :
    D.queryVisits B order P ≤
      (6 * D.unrestrictedChildCount + 2) * D.taskStarts B order P +
        D.matchingVisits B order P := by
  induction order generalizing P with
  | nil =>
    simpa only [queryVisits, taskStarts, matchingVisits, Nat.mul_one,
      Nat.add_right_comm] using D.restricted_collect_queries_le B P
  | cons i order ih =>
    have hq := D.restricted_collect_queries_le B P
    simp only [queryVisits, taskStarts, matchingVisits]
    split
    · have h0 := ih (P.force i false)
      have h1 := ih (P.force i true)
      nlinarith only [hq, h0, h1]
    · simpa only [Nat.add_zero, Nat.mul_one, Nat.add_right_comm] using hq

theorem queryVisits_le (B : ℕ)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (order : List (Fin n))
    (horder : ∀ i ∈ order, i ∈ RepresentationUniverse.topDomain D.leaves)
    (P : MaskRestriction n) :
    D.queryVisits B order P ≤
      (6 * D.unrestrictedChildCount + 2) * D.taskStarts B order P +
        (order.length + 1) * ({ D with maskRestriction := P }).matchingUniverse.card :=
  (D.queryVisits_le_tasks_matching B order P).trans
    (Nat.add_le_add_left (D.matchingVisits_le B hd order horder P) _)

end LowSpaceSubsetSum.RepresentationParentData

end

end OAI
