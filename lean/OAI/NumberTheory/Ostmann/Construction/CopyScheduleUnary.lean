import OAI.NumberTheory.Ostmann.Construction.ScheduledTransferGraph
import OAI.NumberTheory.Ostmann.Construction.ScheduledRegularUnary
import OAI.NumberTheory.Ostmann.Construction.TransferDirectedPhase
import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod

namespace OAI

/-! # The actual unary factors on the copied schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def copyScheduleUnary {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ) :
    (n : ℕ) → FrequencyTree ℤ n → CopyScheduleVertex I n → ℕ → ℂ
  | 0, t, i, p => initial i t p
  | n + 1, t, .inl (true, i), p =>
    copyScheduleUnary χ g pivot initial n t.2.1 i p *
      χ (copyScheduleOrigin n i) p (((frequencyRoot n t.2.1 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        copyScheduleGraph g pivot n i (copySchedulePositive n (pivot n))
  | n + 1, t, .inl (false, i), p =>
    conj (copyScheduleUnary χ g pivot initial n t.2.2 i p) *
      χ (copyScheduleOrigin n i) p (((-frequencyRoot n t.2.2 : ℤ) : ZMod p) * (t.1 : ZMod p)⁻¹) ^
        (-copyScheduleGraph g pivot n i (copySchedulePositive n (pivot n)))
  | n + 1, t, .inr i, p =>
    copyScheduleUnary χ g pivot initial n t.2.1 i p *
      conj (copyScheduleUnary χ g pivot initial n t.2.2 i p)

theorem copyScheduleUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (hinit : ∀ i v p, ‖initial i v p‖ ≤ 1)
    (n : ℕ) (t : FrequencyTree ℤ n) (i : CopyScheduleVertex I n) (p : ℕ) :
    ‖copyScheduleUnary χ g pivot initial n t i p‖ ≤ 1 := by
  induction n with
  | zero => exact hinit i t p
  | succ n ih =>
    rcases i with ⟨c, i⟩ | i
    · cases c
      · rw [copyScheduleUnary, norm_mul, Complex.norm_conj]
        exact (mul_le_mul (ih t.2.2 i) (character_zpow_norm_le_one _ _ _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num)
      · rw [copyScheduleUnary, norm_mul]
        exact (mul_le_mul (ih t.2.1 i) (character_zpow_norm_le_one _ _ _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num)
    · rw [copyScheduleUnary, norm_mul, Complex.norm_conj]
      exact (mul_le_mul (ih t.2.1 i) (ih t.2.2 i) (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The local unary produced by the proved transfer is the restriction of
this single recursively defined schedule unary. -/
theorem copyScheduleUnary_update {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (q : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n → ℕ)
    [∀ i, Fact (q i).Prime]
    (i : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) :
    copiedSlotUnary q (fun h => χ (copyScheduleOrigin n h.val))
      (scheduledRetainedGraph role g pivot n)
      (fun h => copyScheduleUnary χ g pivot initial n t.2.1 h.val (q (.inl (true, h))))
      (fun h => copyScheduleUnary χ g pivot initial n t.2.2 h.val (q (.inl (false, h))))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.1 y.val (q (.inr y)))
      (fun y => copyScheduleUnary χ g pivot initial n t.2.2 y.val (q (.inr y)))
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) t.1 i =
    copyScheduleUnary χ g pivot initial (n + 1) t
      (scheduledOutputVertex role n i).val (q i) := by
  rcases i with ⟨c, h⟩ | y
  · have he : (scheduledOutputVertex role n (.inl (c, h))).val = .inl (c, h.val) := rfl
    rw [he]
    cases c <;> simp [copiedSlotUnary, copyScheduleUnary, scheduledRetainedGraph, div_eq_mul_inv]
  · rfl

end Ostmann

end OAI
