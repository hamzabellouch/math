import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.EquivFin

namespace OAI

namespace RyserCoveringCounterexample

theorem exists_subset_card_slot_injective
    {P I J : Type*} [DecidableEq P] [DecidableEq I] [DecidableEq J]
    (left : P → I) (right : P → J) (D h : ℕ) (S : Finset P)
    (hleft : ∀ i, (S.filter fun x => left x = i).card ≤ D)
    (hright : ∀ j, (S.filter fun x => right x = j).card ≤ D)
    (hlarge : 2 * D * h < S.card) :
    ∃ T : Finset P, T ⊆ S ∧ T.card = h ∧
      Set.InjOn left (T : Set P) ∧ Set.InjOn right (T : Set P) := by
  classical
  induction h generalizing S with
  | zero =>
      refine ⟨∅, Finset.empty_subset S, by simp, ?_, ?_⟩
      · simpa only [Finset.coe_empty] using Set.injOn_empty left
      · simpa only [Finset.coe_empty] using Set.injOn_empty right
  | succ h ih =>
      obtain ⟨x, hx⟩ := Finset.card_pos.mp
        (lt_of_le_of_lt (Nat.zero_le _) hlarge)
      let B := (S.filter fun y => left y = left x) ∪
        (S.filter fun y => right y = right x)
      let U := S \ B
      have hUS : U ⊆ S := Finset.sdiff_subset
      have hB : B.card ≤ 2 * D := by
        calc
          B.card ≤ (S.filter fun y => left y = left x).card +
              (S.filter fun y => right y = right x).card :=
            Finset.card_union_le _ _
          _ ≤ D + D := Nat.add_le_add (hleft (left x)) (hright (right x))
          _ = 2 * D := (Nat.two_mul D).symm
      have hUlarge : 2 * D * h < U.card := by
        have hcount : S.card ≤ U.card + B.card :=
          Finset.card_le_card_sdiff_add_card
        have hexpand : 2 * D * h + 2 * D < S.card := by
          simpa only [Nat.mul_succ] using hlarge
        have hsum : 2 * D * h + 2 * D < U.card + 2 * D :=
          hexpand.trans_le (hcount.trans (Nat.add_le_add_left hB U.card))
        exact Nat.add_lt_add_iff_right.mp hsum
      have hUleft : ∀ i, (U.filter fun y => left y = i).card ≤ D := by
        intro i
        exact (Finset.card_le_card
          (Finset.filter_subset_filter (fun y => left y = i) hUS)).trans (hleft i)
      have hUright : ∀ j, (U.filter fun y => right y = j).card ≤ D := by
        intro j
        exact (Finset.card_le_card
          (Finset.filter_subset_filter (fun y => right y = j) hUS)).trans (hright j)
      obtain ⟨T, hTU, hcard, hTL, hTR⟩ := ih U hUleft hUright hUlarge
      have havoid (y : P) (hy : y ∈ T) :
          left y ≠ left x ∧ right y ≠ right x := by
        have hyU := Finset.mem_sdiff.mp (hTU hy)
        constructor
        · intro heq
          exact hyU.2 (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hyU.1, heq⟩)))
        · intro heq
          exact hyU.2 (Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hyU.1, heq⟩)))
      have hxT : x ∉ T := fun hxT => (havoid x hxT).1 rfl
      refine ⟨insert x T, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hUS (hTU hy)
      · rw [Finset.card_insert_of_notMem hxT, hcard]
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert hxT).2 ⟨hTL, ?_⟩
        rintro ⟨y, hy, heq⟩
        exact (havoid y hy).1 heq
      · rw [Finset.coe_insert]
        refine (Set.injOn_insert hxT).2 ⟨hTR, ?_⟩
        rintro ⟨y, hy, heq⟩
        exact (havoid y hy).2 heq

theorem exists_disjoint_coordinate_sample
    {P I J : Type*} [DecidableEq P] [DecidableEq I] [DecidableEq J]
    (S : Finset P) (left : P → I) (right : P → J) (D h : ℕ)
    (hleft : ∀ i, (S.filter fun x => left x = i).card ≤ D)
    (hright : ∀ j, (S.filter fun x => right x = j).card ≤ D)
    (hlarge : 2 * D * h < S.card) :
    ∃ e : Fin h ↪ ↥S,
      Function.Injective (fun k => left (e k).val) ∧
      Function.Injective (fun k => right (e k).val) := by
  classical
  obtain ⟨T, hTS, hcard, hTL, hTR⟩ :=
    exists_subset_card_slot_injective left right D h S hleft hright hlarge
  let q : Fin h ≃ ↥T := (Finset.equivFinOfCardEq (s := T) hcard).symm
  let e : Fin h ↪ ↥S :=
    { toFun := fun k => ⟨(q k).val, hTS (q k).property⟩
      inj' := by
        intro i j hij
        apply q.injective
        apply Subtype.ext
        exact congrArg (fun x : ↥S => x.val) hij }
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    change left (q i).val = left (q j).val at hij
    exact hTL (q i).property (q j).property hij
  · intro i j hij
    apply q.injective
    apply Subtype.ext
    change right (q i).val = right (q j).val at hij
    exact hTR (q i).property (q j).property hij

end RyserCoveringCounterexample

end OAI
