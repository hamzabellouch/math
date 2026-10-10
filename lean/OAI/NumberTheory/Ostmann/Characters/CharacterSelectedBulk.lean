import OAI.NumberTheory.Ostmann.Characters.CharacterScheduleCounts
import OAI.NumberTheory.Ostmann.Construction.SelectedBulkCoordinates

namespace OAI

/-! # The original m bulk primes exclude the one top prime of each word -/
namespace Ostmann
open scoped Classical BigOperators

/-- The top prime is position zero; the bulk positions are its successors. -/
def characterBulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fin m ↪ (Σ v, Fin (characterSize m r f v)) where
  toFun i := ⟨(true, none), i.succ⟩
  inj' := by
    intro i j h
    have ht : i.succ = j.succ := eq_of_heq (Sigma.mk.inj h).2
    exact Fin.succ_injective m ht

def characterTop {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Σ v, Fin (characterSize m r f v) := ⟨(true, none), ⟨0, Nat.succ_pos m⟩⟩

@[simp] theorem characterBulk_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (i : Fin m) : characterRole k (characterBulk m r f i).1 = .word := rfl

@[simp] theorem characterTop_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    characterRole k (characterTop m r f).1 = .word := rfl

theorem character_word_not_bulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (i : Σ v, Fin (characterSize m r f v))
    (hw : characterRole k i.1 = .word) (hb : i ∉ Set.range (characterBulk m r f)) :
    i = characterTop m r f := by
  obtain ⟨t, ht⟩ := (characterWordEquiv m r f).surjective ⟨i, hw⟩
  have hti : (⟨(true, none), t⟩ : Σ v, Fin (characterSize m r f v)) = i :=
    congrArg Subtype.val ht
  rw [← hti] at hb ⊢
  by_cases hz : t = 0
  · subst t
    rfl
  · obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hz
    subst t
    exact False.elim (hb ⟨j, rfl⟩)

/-- Before copying, exactly one further word slot is outside the bulk. -/
theorem character_original_nonbulk_card {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fintype.card {i : Σ v, Fin (characterSize m r f v) //
      i ∉ Set.range (characterBulk m r f) ∧ characterRole k i.1 ≠ .outside} ≤
        1 + ((∑ j, r j) + 2 * k) := by
  let A := {i : Σ v, Fin (characterSize m r f v) //
    characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside}
  let g : {i : Σ v, Fin (characterSize m r f v) //
      i ∉ Set.range (characterBulk m r f) ∧ characterRole k i.1 ≠ .outside} → Option A :=
    fun i => if h : characterRole k i.val.1 = .word then none
      else some ⟨i.val, h, i.property.2⟩
  have hg : Function.Injective g := by
    intro i j h
    by_cases hi : characterRole k i.val.1 = .word
    · by_cases hj : characterRole k j.val.1 = .word
      · apply Subtype.ext
        exact (character_word_not_bulk m r f i.val hi i.property.1).trans
          (character_word_not_bulk m r f j.val hj j.property.1).symm
      · simp [g, hi, hj] at h
    · by_cases hj : characterRole k j.val.1 = .word
      · simp [g, hi, hj] at h
      · have hh := Option.some.inj (show
          some (⟨i.val, hi, i.property.2⟩ : A) = some ⟨j.val, hj, j.property.2⟩ by
            simpa only [g, dite_eq_right hi, dite_eq_right hj] using h)
        exact Subtype.ext (congrArg (fun x : A => x.val) hh)
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_option, A, characterActiveSlot_card, Nat.add_comm] using hc

theorem character_selected_nonbulk_card {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ) :
    Fintype.card (SelectedNonbulkH
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1)
      n m (characterBulk m r f) (characterBulk_role m r f)) ≤
        2 ^ n * (1 + ((∑ j, r j) + 2 * k)) :=
by
  have h := selectedNonbulkH_card_active
    (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1)
    n m (characterBulk m r f) (characterBulk_role m r f)
  have hc := character_original_nonbulk_card m r f
  simp only [← Nat.card_eq_fintype_card] at h hc ⊢
  exact h.trans (Nat.mul_le_mul_left _ hc)

end Ostmann

end OAI
