import OAI.NumberTheory.Ostmann.Construction.SurvivingSlotCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledActiveCharacters

namespace OAI

/-! # Counting only original active nonword slots

Outside slots cannot enter H. In particular the negative copy of the whole
word must not be charged to the nonbulk harmonic normalization.
-/
namespace Ostmann
open scoped Classical

/-- A binary trace suffices on surviving vertices: at a fixed predecessor,
copying and retaining are mutually exclusive. -/
def survivorTrace {I : Type*} : (n : ℕ) → CopyScheduleVertex I n → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | n + 1, .inl (b, i) => Fin.snoc (survivorTrace n i) b
  | n + 1, .inr i => Fin.snoc (survivorTrace n i) false

theorem survivorTrace_origin_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i j : CopyScheduleVertex I n)
    (hi : CopyScheduleSurvives role n i) (hj : CopyScheduleSurvives role n j)
    (ht : survivorTrace n i = survivorTrace n j)
    (ho : copyScheduleOrigin n i = copyScheduleOrigin n j) : i = j := by
  induction n with
  | zero => exact ho
  | succ n ih =>
    cases i with
    | inl ib =>
      rcases ib with ⟨b, i⟩
      cases j with
      | inl jb =>
        rcases jb with ⟨c, j⟩
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hbc : b = c := by
          simpa only [survivorTrace, Fin.snoc_last] using congrFun ht (Fin.last n)
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        subst c
        rfl
      | inr j =>
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        exact False.elim (Bool.noConfusion (hi.2.symm.trans hj.2.1))
    | inr i =>
      cases j with
      | inl jb =>
        rcases jb with ⟨b, j⟩
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        exact False.elim (Bool.noConfusion (hj.2.symm.trans hi.2.1))
      | inr j =>
        have ht' : survivorTrace n i = survivorTrace n j := by
          funext t
          simpa only [survivorTrace, Fin.snoc_castSucc] using congrFun ht t.castSucc
        have hij := ih i j hi.1 hj.1 ht' ho
        subst j
        rfl

theorem copyScheduleRole_origin_word {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : CopyScheduleVertex I n) (hi : role (copyScheduleOrigin n i) = .word) :
    copyScheduleRole role n i = .word := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · change (copyScheduleRole role n i).afterCopy b = .word
      rw [ih i hi]
      rfl
    · exact ih i hi

/-- The coefficient counts only original slots which can actually enter H. -/
theorem scheduledNonbulkH_card_active {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (ScheduledNonbulkH role n) ≤
      2 ^ n * Fintype.card {i : I // role i ≠ .word ∧ role i ≠ .outside} := by
  let code : ScheduledNonbulkH role n →
      (Fin n → Bool) × {i : I // role i ≠ .word ∧ role i ≠ .outside} :=
    fun h => (survivorTrace n h.val.val, ⟨copyScheduleOrigin n h.val.val, by
      constructor
      · intro hw
        exact h.property (copyScheduleRole_origin_word role n h.val.val hw)
      · exact copyScheduleH_origin_not_outside role n h.val⟩)
  have hc : Function.Injective code := by
    intro i j h
    apply Subtype.ext
    apply Subtype.ext
    exact survivorTrace_origin_injective role n i.val.val j.val.val i.val.property.1
      j.val.property.1 (congrArg Prod.fst h)
      (congrArg (fun z => z.2.val) h)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    using Fintype.card_le_of_injective code hc

end Ostmann

end OAI
