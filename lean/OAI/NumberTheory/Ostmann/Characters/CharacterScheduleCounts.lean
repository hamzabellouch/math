import OAI.NumberTheory.Ostmann.Characters.CharacterScheduleRoles
import OAI.NumberTheory.Ostmann.Construction.ActiveNonbulkCount

namespace OAI

/-! # Exact active nonbulk count in the finite character schedule -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def characterActiveSlotEquiv {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    ((Σ j : Fin k, Fin (r j)) ⊕ (Fin k × Bool)) ≃
      {i : Σ v, Fin (characterSize m r f v) //
        characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside} := by
  let toSlot : ((Σ j : Fin k, Fin (r j)) ⊕ (Fin k × Bool)) →
      {i : Σ v, Fin (characterSize m r f v) //
        characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside} := fun x =>
    match x with
    | .inl ⟨j, t⟩ => ⟨⟨characterPivotAtom j, t⟩, by simp⟩
    | .inr (j, b) => ⟨characterAnchor m r f j b, by simp⟩
  refine Equiv.ofBijective toSlot ⟨?_, ?_⟩
  · rintro (⟨i, t⟩ | ⟨i, b⟩) (⟨j, u⟩ | ⟨j, c⟩) h
    · have hp := congrArg (fun x => x.val.1) h
      have hij : i = j := by simpa [toSlot, characterPivotAtom] using hp
      subst j
      have ht : t = u := by
        have hh := congrArg Subtype.val h
        exact eq_of_heq (Sigma.mk.inj hh).2
      subst u
      rfl
    · have hp := congrArg (fun x => x.val.1) h
      simp [toSlot, characterPivotAtom, characterAnchor, characterAnchorAtom] at hp
    · have hp := congrArg (fun x => x.val.1) h
      simp [toSlot, characterPivotAtom, characterAnchor, characterAnchorAtom] at hp
    · have hp := congrArg (fun x => x.val.1) h
      have hij : i = j ∧ b = c := by
        simpa [toSlot, characterAnchor, characterAnchorAtom] using hp
      rcases hij with ⟨rfl, rfl⟩
      rfl
  · rintro ⟨⟨⟨b, c⟩, t⟩, hw, ho⟩
    cases b with
    | false => simp [characterRole, signedAtomRole] at ho
    | true =>
      cases c with
      | none => simp at hw
      | some c =>
        rcases c with j | ⟨j, b⟩ | u
        · exact ⟨.inl ⟨j, t⟩, rfl⟩
        · refine ⟨.inr (j, b), ?_⟩
          have ht : t = (⟨0, Nat.zero_lt_one⟩ : Fin 1) := by
            apply Fin.ext
            have hlt : t.val < 1 := t.isLt
            change t.val = 0
            omega
          subst t
          rfl
        · simp [characterRole, signedAtomRole, characterPositiveRole] at ho

theorem characterActiveSlot_card {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fintype.card {i : Σ v, Fin (characterSize m r f v) //
      characterRole k i.1 ≠ .word ∧ characterRole k i.1 ≠ .outside} =
        (∑ j, r j) + 2 * k := by
  rw [← Fintype.card_congr (characterActiveSlotEquiv m r f)]
  simp [Fintype.card_sigma, Nat.mul_comm]

theorem characterNonbulkH_card {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ) :
    Fintype.card (ScheduledNonbulkH
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n) ≤
        2 ^ n * ((∑ j, r j) + 2 * k) := by
  simpa only [characterActiveSlot_card] using
    scheduledNonbulkH_card_active
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n

end Ostmann

end OAI
