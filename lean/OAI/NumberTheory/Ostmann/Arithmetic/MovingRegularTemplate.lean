import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotNodup

namespace OAI

/-! # The actual small and bulk slots at a moving-giant level -/

namespace Ostmann
open scoped Classical BigOperators

/-- Each surviving leaf has its remaining small slots and its original bulk. -/
abbrev MovingRegularSlot (n r m : ℕ) := TreeLeafIndex n × (Fin r ⊕ Fin m)

def movingTemplateBulk (n r m : ℕ) : (TreeLeafIndex n × Fin m) ↪ MovingRegularSlot n r m where
  toFun j := (j.1, .inr j.2)
  inj' := by intro i j h; cases i; cases j; cases h; rfl

noncomputable def movingTemplateSmall (n r m : ℕ) : TreeLeafTuple (List (MovingRegularSlot n r m)) n :=
  bulkSlotLeaves n r (fun j => (j.1, .inl j.2))

theorem movingTemplateSmall_length (n r m : ℕ) :
    MovingLeafLengthLE n (movingTemplateSmall n r m) r := bulkSlotLeaves_length n r _

theorem movingTemplateSmall_not_bulk (n r m : ℕ) :
    ∀ i ∈ flattenMovingSlots n (movingTemplateSmall n r m), i ∉ Set.range (movingTemplateBulk n r m) := by
  intro i hi hbulk
  obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ i).mp hi
  obtain ⟨k, hk⟩ := hbulk
  have hs : (Sum.inr k.2 : Fin r ⊕ Fin m) = .inl j.2 :=
    congrArg (fun z : MovingRegularSlot n r m => z.2) hk
  cases hs

theorem movingRegularSlot_card (n r m : ℕ) :
    Fintype.card (MovingRegularSlot n r m) = 2 ^ n * (r + m) := by
  simp only [MovingRegularSlot, Fintype.card_prod, card_treeLeafIndex, Fintype.card_sum,
    Fintype.card_fin]

/-- Restoring a removed type puts its four sampled compensation primes back
before the surviving small slots. Bulk labels retain their identity. -/
def movingReverseTemplate (n r m : ℕ) :
    ((TreeLeafIndex n × Fin 4) ⊕ MovingRegularSlot n r m) ≃ MovingRegularSlot n (4 + r) m where
  toFun
    | .inl (j, i) => (j, .inl (Fin.castAdd r i))
    | .inr (j, .inl i) => (j, .inl (Fin.natAdd 4 i))
    | .inr (j, .inr i) => (j, .inr i)
  invFun
    | (j, .inl i) => Fin.addCases (fun a => .inl (j, a)) (fun b => .inr (j, .inl b)) i
    | (j, .inr i) => .inr (j, .inr i)
  left_inv := by
    intro x
    rcases x with (⟨j, i⟩ | ⟨j, i | i⟩) <;> simp
  right_inv := by
    rintro ⟨j, i | i⟩
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
    · rfl

@[simp] theorem movingReverseTemplate_bulk (n r m : ℕ) (j : TreeLeafIndex n × Fin m) :
    movingReverseTemplate n r m (.inr (movingTemplateBulk n r m j)) =
      movingTemplateBulk n (4 + r) m j := rfl

@[simp] theorem movingReverseTemplate_compensation (n r m : ℕ) (j : TreeLeafIndex n × Fin 4) :
    movingReverseTemplate n r m (.inl j) = (j.1, .inl (Fin.castAdd r j.2)) := rfl

end Ostmann

end OAI
