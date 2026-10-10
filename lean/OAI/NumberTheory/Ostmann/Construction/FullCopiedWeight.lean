import OAI.NumberTheory.Ostmann.Construction.FullAtomTransferWeight
import OAI.NumberTheory.Ostmann.Construction.InsertedAtomAssignment

namespace OAI

/-! # The full transferred weight in the actual two branch assignments -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem scheduleAtomLeft_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ) :
    scheduleAtomLeft role ⟨n + 1, scheduledCopiedAssignment role n u l r⟩ = ∏ h, l h := rfl

theorem scheduleAtomRight_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ) :
    scheduleAtomRight role ⟨n + 1, scheduledCopiedAssignment role n u l r⟩ = ∏ h, r h := rfl

/-- The parent coefficient is exactly the product of the two inherited
coefficients at the forced pivot, with only the new root tests added. -/
theorem fullAtomTransferWeight_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (P : ℕ)
    (hP : ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, scheduledCopiedAssignment role n u l r⟩
      s (frequencyRoot n t) (frequencyRoot n t') P) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (scheduledCopiedAssignment role n u l r) (s, t, t') =
      if fullAtomRootGuard role ranges n (scheduledCopiedAssignment role n u l r) P s then
        fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n P l u) t *
        conj (fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n P r u) t') else 0 := by
  rw [fullAtomTransferWeight_node role childBound pivotBound ranges leaf n _ _ P hP,
    reverseCopiedAtoms_eq_inserted, reverseCopiedAtoms_eq_inserted]
  rfl

end Ostmann

end OAI
