import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTree
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRepresentativeLineSystem

namespace OAI

/-! # An actual occurrence for every internal sample class -/

namespace Ostmann
open scoped Classical

theorem movingCompensationSlots_mem {A : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) (t : TreeLeafIndex n) (j : Fin 4) :
    treeLeafTupleEquiv (Fin 4 → A) n a t j ∈
      flattenMovingSlots n (movingCompensationSlots n a) := by
  induction n with
  | zero => exact List.mem_ofFn.mpr ⟨j, rfl⟩
  | succ n ih =>
    cases t with
    | inl t => exact List.mem_append_left _ (ih a.1 t)
    | inr t => exact List.mem_append_right _ (ih a.2 t)

/-- Each independent draw has a genuine node occurrence in the constructed
history; subsequent copies in regular lists are irrelevant to this witness. -/
theorem movingSample_occurs {A : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List A) n) (a : MovingSampleSlots A n)
    (i : MovingSampleIndex n) :
    ∃ o ∈ (buildMovingSlotData n t small bulk a).occurrences,
      movingSampleCoordinates A n a i ∈ o.current.compensationSlots := by
  induction a with
  | leaf => exact Empty.elim i
  | @node n a l r hl hr =>
    let U := flattenMovingSlots n (movingCompensationSlots n a)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let L := buildMovingSlotData n t.2.1
      (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) bulk.1 l
    let R := buildMovingSlotData n t.2.2
      (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) bulk.2 r
    change ∃ o ∈ (MovingSlotData.node t.1 CL CR U L R).occurrences,
      movingSampleCoordinates A (n + 1) (.node a l r) i ∈ o.current.compensationSlots
    rcases i with ⟨ti, j⟩ | ⟨b, i⟩
    · refine ⟨⟨n + 1, MovingSlotData.step t.1 CL CR U L R false, []⟩, List.mem_cons_self, ?_⟩
      exact movingCompensationSlots_mem n a ti j
    · cases b with
      | false =>
        obtain ⟨o, ho, hi⟩ := hr t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n a) small.2) bulk.2 i
        refine ⟨o.extend (MovingSlotData.step t.1 CL CR U L R false), ?_, hi⟩
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))
      | true =>
        obtain ⟨o, ho, hi⟩ := hl t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n a) small.1) bulk.1 i
        refine ⟨o.extend (MovingSlotData.step t.1 CL CR U L R true), ?_, hi⟩
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))

/-- A representative occurrence exists for every nonempty internal class of
the actual paired pattern, without an extra arithmetic assumption. -/
theorem movingPattern_representative_nonempty {B C : Type*}
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (c : C) :
    Nonempty (MovingPairRepresentativeOccurrences
      (fun side => movingPatternSlotData n (t side) (small side) (bulk side) pattern side) (.inr c)) := by
  let i := rep c
  have h := movingSample_occurs n (t i.val.1)
    (treeLeafMap (List.map Sum.inl) n (small i.val.1)) (treeLeafMap (List.map Sum.inl) n (bulk i.val.1))
    (movingPatternSamples (B ⊕ C) n (Sum.inr ∘ pattern) i.val.1) i.val.2
  simp only [movingPatternSamples, Equiv.apply_symm_apply, Function.comp_apply, i.property] at h
  obtain ⟨o, ho, hi⟩ := h
  change o ∈ (movingPatternSlotData n (t i.val.1) (small i.val.1) (bulk i.val.1) pattern i.val.1).occurrences at ho
  obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
  refine ⟨⟨i.val.1, ⟨⟨k, hk⟩, ?_⟩⟩⟩
  simpa only [List.get_eq_getElem, hko] using hi

noncomputable def movingPatternRepresentative {B C : Type*}
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (c : C) :
    MovingPairRepresentativeOccurrences
      (fun side => movingPatternSlotData n (t side) (small side) (bulk side) pattern side) (.inr c) :=
  Classical.choice (movingPattern_representative_nonempty n t small bulk pattern rep c)

end Ostmann

end OAI
