import OAI.Combinatorics.ContingencyTables.Transport.TwoLiftStates

namespace OAI

/-! # The actual doubled labels form disjoint covering slots -/

namespace ContingencyTables.PairedLabels

open scoped BigOperators Classical
open CommonBasesFPRAS TwoLiftStates

variable {P : Type*}

private lemma mapped_fresh (l : List P) (hl : l.Nodup) (B : Set (P×Bool))
    (hB : ∀ p ∈ l, ∀ b, (p,b)∉B) : SlotsFresh (l.map pair) B := by
  induction l generalizing B with
  | nil => trivial
  | cons p l ih =>
    have hd := List.nodup_cons.mp hl
    refine ⟨?_,hB p (by simp) false,hB p (by simp) true,?_⟩
    · intro he
      exact Bool.false_ne_true (congrArg Prod.snd he)
    · apply ih hd.2
      intro q hq b hm
      rcases hm with he|he|hm
      · have hqp : q=p := congrArg Prod.fst he
        exact hd.1 (hqp ▸ hq)
      · have hqp : q=p := congrArg Prod.fst he
        exact hd.1 (hqp ▸ hq)
      · exact hB q (by simp [hq]) b hm

variable [Fintype P]

theorem fresh : SlotsFresh (pairs : List ((P×Bool)×(P×Bool))) ∅ :=
  mapped_fresh Finset.univ.toList (Finset.nodup_toList _) _ (by intro p hp b; exact Set.notMem_empty _)

theorem cover : pairSupport (pairs : List ((P×Bool)×(P×Bool)))=Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨p,b⟩
  refine ⟨pair p,pair_mem p,?_⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem length : (pairs : List ((P×Bool)×(P×Bool))).length=Fintype.card P := by
  simp [pairs]

end ContingencyTables.PairedLabels

end OAI
