import OAI.NumberTheory.Ostmann.Construction.ScheduledActiveCharacters
import OAI.NumberTheory.Ostmann.Construction.ConstituentInvariantCharacter

namespace OAI

/-! # The positive and conjugate atom copies retain their original characters -/

namespace Ostmann

/-- The first squared-amplitude branch supplies the copied roles. The other
branch is retained outside throughout the transfer schedule. -/
def signedAtomRole {I : Type*} (role : I → CopyScheduleRole) :
    Bool × I → CopyScheduleRole := fun i => if i.1 then role i.2 else .outside

noncomputable def signedAtomCharacter {I : Type*} (size : I → ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) :
    (Σ i : Bool × I, Fin (size i.2)) → ∀ p : ℕ, DirichletCharacter ℂ p :=
  fun i p => if i.1.1 then χ p else (χ p)⁻¹

theorem signedAtomCharacter_active {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (i : Σ j : Bool × I, Fin (size j.2))
    (hi : signedAtomRole role i.1 ≠ .outside) : signedAtomCharacter size χ i = χ := by
  rcases i with ⟨⟨b, i⟩, k⟩
  cases b with
  | false => exact False.elim (hi rfl)
  | true => rfl

/-- Even negative transfer copies keep the character of their original atom.
Every prime-slot matching in H therefore preserves the character assignment. -/
theorem signedAtomCharacter_matching {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH
      (fun i : Σ j : Bool × I, Fin (size j.2) => signedAtomRole role i.1) n))
    (h : CopyScheduleH
      (fun i : Σ j : Bool × I, Fin (size j.2) => signedAtomRole role i.1) n) :
    signedAtomCharacter size χ (copyScheduleOrigin n (e h).val) =
      signedAtomCharacter size χ (copyScheduleOrigin n h.val) :=
  scheduled_active_characters_invariant _ _ χ
    (signedAtomCharacter_active role size χ) n e h

end Ostmann

end OAI
