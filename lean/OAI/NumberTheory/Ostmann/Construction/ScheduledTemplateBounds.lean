import OAI.NumberTheory.Ostmann.Construction.ScheduledWordTemplate

namespace OAI

/-! # Word-size bounds for the constructed copied-atom template -/

namespace Ostmann

open scoped Classical

theorem copyScheduleVertex_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (CopyScheduleVertex I n) = 3 ^ n * Fintype.card I := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact Fintype.card_congr (Equiv.refl I)
  | succ n ih =>
    change Fintype.card ((Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

theorem copyScheduleAtoms_zero_card {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    Fintype.card (CopyScheduleAtoms role 0) = Fintype.card I := by
  let e : CopyScheduleAtoms role 0 ≃ I :=
    ⟨Subtype.val, fun i => ⟨i, True.intro⟩, (by intro i; rfl), (by intro i; rfl)⟩
  exact Fintype.card_congr e

theorem copyScheduleH_card_le {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleH role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

def scheduledTemplateWordBound (I : Type*) [Fintype I] (n : ℕ) : ℕ :=
  2 * 3 ^ n * Fintype.card I + 4

theorem scheduledTemplateWordBound_pos (I : Type*) [Fintype I] (n : ℕ) :
    1 ≤ scheduledTemplateWordBound I n := by
  unfold scheduledTemplateWordBound
  omega

/-- For fixed depth the word-size parameter is linear in the original
number of atoms. All formula bounds therefore stay polynomial in that number. -/
theorem scheduledWordTemplate_size {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ)
    (path : List Bool) (current : CopyScheduleAtoms role n → σ) :
    (scheduledWordTemplate role address childBound pivotBound n path current).WordsBounded
      (scheduledTemplateWordBound I n) := by
  apply scheduledWordTemplate_words_bounded
  · rw [copyScheduleAtoms_zero_card]
    unfold scheduledTemplateWordBound
    have hp : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by omega)
    nlinarith
  · intro j hj
    have hcard := copyScheduleH_card_le role j
    have hpow : 3 ^ j ≤ 3 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have hm := Nat.mul_le_mul_right (Fintype.card I) hpow
    unfold scheduledTemplateWordBound
    nlinarith

end Ostmann

end OAI
