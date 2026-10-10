import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedSupport
import OAI.NumberTheory.Ostmann.Construction.TransferredPivotSubstitution

namespace OAI

/-! # The supported next coefficient retains the same positive integer pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_copied_validPivot {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (T : Finset ℕ)
    (hT : ∀ M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) t ≠ 0 → M ∈ T)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
      (copiedConstituentAtomValues role size n P u l r) (s, t, t') ≠ 0) :
    validTransferredPivot T
      (frequencyRoot n t * (∏ h, (r h : ℕ)) - frequencyRoot n t' * (∏ h, (l h : ℕ))) s := by
  obtain ⟨hg, M, hM, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
    (n + 1) (copiedConstituentAtomValues role size n P u l r) (s, t, t') hw
  have hroot := ((fullAtomWeightGuard_node role childBound pivotBound ranges n
    (copiedConstituentAtomValues role size n P u l r) (s, t, t') M hM).mp hg).1
  have hchild := hw
  unfold copiedConstituentAtomValues at hchild hroot
  rw [fullAtomTransferWeight_copied role childBound pivotBound ranges leaf n _ _ _ s t t' M hM,
    ite_eq_left hroot] at hchild
  apply validTransferredPivot_of_eq T _ s hM.root_ne_zero M hM.pivot_pos
    (hT M hM.pivot_pos hM.pivot_bound (mul_ne_zero_iff.mp hchild).1)
  have hr := hM.relation
  change frequencyRoot n t *
      (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) -
      frequencyRoot n t' *
      (scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) = s * M at hr
  rwa [copiedConstituentAtomValues_left, copiedConstituentAtomValues_right] at hr

end Ostmann

end OAI
