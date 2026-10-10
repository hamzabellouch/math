import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.Computability.PerfectCompleteness.Construction.TreeSourceSpaces
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys
import OAI.Computability.PerfectCompleteness.Reduction.SourceGame

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport
open scoped BigOperators

variable {n : Nat} {Y : Type*}

abbrev KeyLabel (k : Key n) := ↥k.partition

instance KeyLabel_finite (k : Key n) : Finite (KeyLabel k) := by
  let : Finite ReducedValue := ReducedDomains.reducedValue_finite
  exact Finite.of_injective (fun P : KeyLabel k => P.val) Subtype.val_injective

instance keyLabel_nonempty (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Nonempty (KeyLabel (key side slots f)) := by
  change Nonempty (Label slots f)
  infer_instance

theorem label_finite (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Finite (Label slots f) := by
  infer_instance

theorem label_nonempty (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Nonempty (Label slots f) := by
  infer_instance

theorem card_label_le_output [Finite Y] (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Nat.card (Label slots f) ≤ Nat.card Y :=
  Nat.card_le_card_of_injective (restore slots f) (restore_injective slots f)

theorem card_label_le_assignment (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Nat.card (Label slots f) ≤ Nat.card (Assignment slots) :=
  ReducedPartition.card_parts_le (reduction slots f) f

def answerEquivFinSeven (signs : SourceClause.Triple) : Answer signs ≃ Fin 7 where
  toFun u := SourceGame.encodeLabel signs u.val
    ((SourceClause.mem_satisfyingTriples signs u.val).mp u.property)
  invFun i := ⟨SourceGame.decodeLabel signs i, SourceGame.decodeLabel_mem signs i⟩
  left_inv u := by
    apply Subtype.ext
    exact SourceGame.decodeLabel_encodeLabel signs u.val _
  right_inv i := by
    apply SourceGame.decodeLabel_injective signs
    exact SourceGame.decodeLabel_encodeLabel signs (SourceGame.decodeLabel signs i) _

theorem card_answer (signs : SourceClause.Triple) : Nat.card (Answer signs) = 7 := by
  simpa only [Nat.card_fin] using Nat.card_congr (answerEquivFinSeven signs)

theorem card_slotDomain_le_seven (s : Slot) : Nat.card s.Domain ≤ 7 := by
  cases s with
  | clause occurrence variableIDs signs => exact (card_answer signs).le
  | bit variableID =>
      change Nat.card Bool ≤ 7
      simp

theorem card_assignment_le_seven_pow (slots : Fin n → Slot) :
    Nat.card (Assignment slots) ≤ 7 ^ n := by
  change Nat.card (∀ i : Fin n, (slots i).Domain) ≤ _
  rw [Nat.card_pi]
  calc
    (∏ i : Fin n, Nat.card (slots i).Domain) ≤ ∏ _i : Fin n, (7 : Nat) :=
      Finset.prod_le_prod (fun i _ => card_slotDomain_le_seven (slots i))
    _ = 7 ^ n := by simp

theorem card_label_le_seven_pow (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Nat.card (Label slots f) ≤ 7 ^ n :=
  (card_label_le_assignment slots f).trans (card_assignment_le_seven_pow slots)

theorem card_keyLabel_le_output [Finite Y] (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Nat.card (KeyLabel (key side slots f)) ≤ Nat.card Y :=
  card_label_le_output slots f

theorem card_keyLabel_le_seven_pow (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Nat.card (KeyLabel (key side slots f)) ≤ 7 ^ n :=
  card_label_le_seven_pow slots f

end PerfectCompleteness.CanonicalKeys

end

end OAI
