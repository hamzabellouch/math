import Mathlib.NumberTheory.DirichletCharacter.Basic
import OAI.NumberTheory.Ostmann.Construction.CopyScheduleSupport
import OAI.NumberTheory.Ostmann.Construction.ScheduledRegularUnary

namespace OAI

/-! # Only original positive roles can occur in the active H block -/

namespace Ostmann

theorem copyScheduleRole_origin_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (v : CopyScheduleVertex I n) (hv : role (copyScheduleOrigin n v) = .outside) :
    copyScheduleRole role n v = .outside := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rcases v with ⟨b, v⟩ | v
    · change (copyScheduleRole role n v).afterCopy b = .outside
      have h := ih v hv
      rw [h]
      rfl
    · exact ih v hv

theorem copyScheduleH_origin_not_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (h : CopyScheduleH role n) : role (copyScheduleOrigin n h.val) ≠ .outside := by
  intro he
  have hh := h.property.2
  rw [copyScheduleRole_origin_outside role n h.val he] at hh
  cases hh

theorem scheduled_active_characters_invariant {I : Type*}
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χ₀ : ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i, role i ≠ .outside → χ i = χ₀)
    (n : ℕ) (e : Equiv.Perm (CopyScheduleH role n)) (h : CopyScheduleH role n) :
    χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val) := by
  rw [hχ _ (copyScheduleH_origin_not_outside role n (e h)),
    hχ _ (copyScheduleH_origin_not_outside role n h)]

end Ostmann

end OAI
