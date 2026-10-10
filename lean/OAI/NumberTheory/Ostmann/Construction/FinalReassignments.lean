import Mathlib.Data.Fintype.Sum
import OAI.NumberTheory.Ostmann.Construction.FinalParityPaths

namespace OAI

/-! # The actual independent, parity-preserving bulk reassignments -/

namespace Ostmann

open scoped Classical

abbrev ParityPathSum (n : ℕ) := ParityPaths n 1 ⊕ ParityPaths n (-1)

def parityPathValue {n : ℕ} : ParityPathSum n → (Fin (n + 1) → Bool)
  | .inl t => t.val
  | .inr t => t.val

theorem parityPathValue_injective (n : ℕ) : Function.Injective (@parityPathValue n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext hab)
    | inr b => have := a.property.symm.trans ((congrArg finalCopyParity hab).trans b.property); omega
  | inr a =>
    cases b with
    | inl b => have := a.property.symm.trans ((congrArg finalCopyParity hab).trans b.property); omega
    | inr b => exact congrArg Sum.inr (Subtype.ext hab)

noncomputable def parityPathSumEquiv (n : ℕ) : ParityPathSum n ≃ (Fin (n + 1) → Bool) :=
  Equiv.ofBijective parityPathValue ⟨parityPathValue_injective n, by
    intro t
    rcases copyPathParity_sign (finiteCopyPath t) (n + 1) with h | h
    · exact ⟨.inl ⟨t, h⟩, rfl⟩
    · exact ⟨.inr ⟨t, h⟩, rfl⟩⟩

def paritySlotPerm {n m : ℕ} (e : FinalParityReassignments n m) :
    Equiv.Perm (ParityPathSum n × Fin m) where
  toFun x := ((Equiv.sumCongr (e x.2).1 (e x.2).2) x.1, x.2)
  invFun x := ((Equiv.sumCongr (e x.2).1 (e x.2).2).symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

theorem paritySlotPerm_preserves_parity {n m : ℕ} (e : FinalParityReassignments n m)
    (x : ParityPathSum n × Fin m) :
    finalCopyParity (parityPathValue (paritySlotPerm e x).1) = finalCopyParity (parityPathValue x.1) := by
  rcases x with ⟨t, i⟩
  cases t with
  | inl t => exact ((e i).1 t).property.trans t.property.symm
  | inr t => exact ((e i).2 t).property.trans t.property.symm

theorem paritySlotPerm_preserves_position {n m : ℕ} (e : FinalParityReassignments n m)
    (x : ParityPathSum n × Fin m) : (paritySlotPerm e x).2 = x.2 := rfl

theorem paritySlotPerm_injective {n m : ℕ} :
    Function.Injective (@paritySlotPerm n m) := by
  intro e f hef
  funext i
  apply Prod.ext
  · apply Equiv.ext
    intro t
    have h := congrArg (fun g => (g (.inl t, i)).1) hef
    exact Sum.inl.inj h
  · apply Equiv.ext
    intro t
    have h := congrArg (fun g => (g (.inr t, i)).1) hef
    exact Sum.inr.inj h

/-- Distinct members of the constructed reassignment family move some prime
to a path with a different anchor code, while retaining its final parity. -/
theorem distinct_reassignments_change_code {n m : ℕ}
    (α : Fin (n + 1) → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ x : ParityPathSum n × Fin m,
      finiteAnchorCode α (parityPathValue (paritySlotPerm e x).1) ≠
        finiteAnchorCode α (parityPathValue (paritySlotPerm f x).1) := by
  by_contra h
  push Not at h
  apply hef
  apply paritySlotPerm_injective
  apply Equiv.ext
  intro x
  apply Prod.ext
  · apply parityPathValue_injective n
    apply finiteAnchorCode_final_injective α hα
    apply Prod.ext
    · exact h x
    · exact (paritySlotPerm_preserves_parity e x).trans (paritySlotPerm_preserves_parity f x).symm
  · rfl

end Ostmann

end OAI
