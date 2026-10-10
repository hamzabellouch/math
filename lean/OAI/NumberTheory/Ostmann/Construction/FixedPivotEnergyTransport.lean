import OAI.NumberTheory.Ostmann.Construction.ConstituentEnergyTransport
import OAI.NumberTheory.Ostmann.Construction.ConstituentPartitionAssignment

namespace OAI

/-! # Retaining selected-prime energy with an externally fixed composite pivot -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def scheduledReplacePivot {I : Type*} (role : I → CopyScheduleRole)
    (n M : ℕ) (base : CopyScheduleAtoms role n → ℕ) : CopyScheduleAtoms role n → ℕ :=
  fun a => if (copyScheduleRole role n a.val).erasedAt n then M else base a

/-- Replacing the current pivot never changes a selected original word prime. -/
theorem scheduledReplacePivot_wordLeafScale {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n M : ℕ)
    (base : CopyScheduleAtoms role n → ℕ) (x : TreeLeafIndex n → ℕ) :
    scheduledReplacePivot role n M (wordLeafScale role i hi n base x) =
      wordLeafScale role i hi n (scheduledReplacePivot role n M base) x := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t =>
    simp only [wordLeafPartition_leaf, scheduledReplacePivot, wordLeafSlot_role,
      CopyScheduleRole.erasedAt, Bool.false_eq_true, ↓reduceIte, wordLeafScale_leaf]
  | inr v =>
    simp only [wordLeafPartition_outside, scheduledReplacePivot, wordLeafScale_outside]

/-- The replaced assignment is exactly the original H/Y assignment with M inserted. -/
theorem scheduledReplacePivot_eq_inserted {I : Type*}
    (role : I → CopyScheduleRole) (n M : ℕ) (base : CopyScheduleAtoms role n → ℕ) :
    scheduledReplacePivot role n M base = scheduledInsertedAtoms role n M
      (fun h => base ⟨h.val, h.property.1⟩) (fun y => base ⟨y.val, y.property.1⟩) := by
  funext v
  obtain ⟨v, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases v with p | h | y
  · rw [scheduledInsertedAtoms_pivot]
    simp [scheduledReplacePivot,
      copyScheduleRole_positive role p.val n p.property n, CopyScheduleRole.erasedAt]
  · change scheduledReplacePivot role n M base ⟨h.val, h.property.1⟩ = _
    rw [show scheduledInsertedAtoms role n M
        (fun h => base ⟨h.val, h.property.1⟩) (fun y => base ⟨y.val, y.property.1⟩)
        (scheduledPartitionEquiv role n (.inr (.inl h))) = base ⟨h.val, h.property.1⟩ by
      simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]]
    have he : (copyScheduleRole role n h.val).erasedAt n = false := by
      have hc := h.property.2
      cases hr : copyScheduleRole role n h.val <;>
        simp_all [CopyScheduleRole.copiedAt, CopyScheduleRole.erasedAt]
      omega
    simp only [scheduledReplacePivot, he, Bool.false_eq_true, ↓reduceIte]
  · change scheduledReplacePivot role n M base ⟨y.val, y.property.1⟩ = _
    rw [show scheduledInsertedAtoms role n M
        (fun h => base ⟨h.val, h.property.1⟩) (fun y => base ⟨y.val, y.property.1⟩)
        (scheduledPartitionEquiv role n (.inr (.inr y))) = base ⟨y.val, y.property.1⟩ by
      simp only [scheduledInsertedAtoms, Equiv.symm_apply_apply]]
    simp only [scheduledReplacePivot, y.property.2.2, Bool.false_eq_true, ↓reduceIte]

/-- The full original product prior can be retained while the pivot is fixed
externally. Its unused prime coordinates integrate out with total mass one. -/
theorem constituent_fixedPivot_energy_transport {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n M : ℕ)
    (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
    (hsub : ∀ j, cells j ⊆ P) (hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
    (F : D → (CopyScheduleAtoms role n → ℕ) → ℝ) (B : ℝ)
    (hsection : ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ d, ∑ x : TreeLeafIndex n → P, (∏ t, primeSubsetPrior P (cells i) (x t)) *
        F d (wordLeafScale role i.1 hi n base (fun t => (x t : ℕ)))) ≤ B) :
    (∑ d, ∑ q : SurvivingConstituent role size n → P,
      scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
        (fun j => primeSubsetPrior P (cells j)) q *
        F d (scheduledReplacePivot role n M
          (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))) ≤ B := by
  apply constituent_energy_transport role size i hi n P cells hsub hmass
    (fun d base => F d (scheduledReplacePivot role n M base)) B
  intro base
  simp_rw [scheduledReplacePivot_wordLeafScale]
  exact hsection (scheduledReplacePivot role n M base)

end Ostmann

end OAI
