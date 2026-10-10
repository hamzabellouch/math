import OAI.NumberTheory.Ostmann.Construction.ConstituentAtomProductBounds

namespace OAI

/-! # Whole-atom products on every nonzero fixed-pivot history -/
namespace Ostmann
open scoped Classical BigOperators

theorem fullAtomTransferWeight_inserted_H_product_bounds {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (t : FrequencyTree ℤ n)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) (M : ℕ)
    (hw : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t ≠ 0) :
    (∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val)) ≤ (∏ h, l h) ∧
      (∏ h, l h) ≤ ∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val) := by
  have hr := (atomIntervalRanges_holds_iff role lo hi n _).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf n _ t hw r hr)
  have hh (h : CopyScheduleH role n) :
      lo (copyScheduleOrigin n h.val) ≤ ∏ k, l (constituentH role size n h k) ∧
      (∏ k, l (constituentH role size n h k)) ≤ hi (copyScheduleOrigin n h.val) := by
    simpa only [scheduledInsertedAtoms_H] using hr ⟨h.val, h.property.1⟩
  rw [← constituentH_product role size n l]
  exact ⟨Finset.prod_le_prod (fun h _ => (hh h).1),
    Finset.prod_le_prod (fun h _ => (hh h).2)⟩

end Ostmann

end OAI
