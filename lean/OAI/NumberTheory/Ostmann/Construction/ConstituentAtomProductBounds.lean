import OAI.NumberTheory.Ostmann.Construction.ConstituentIntervalSupport
import OAI.NumberTheory.Ostmann.Construction.ConstituentPriorBounds

namespace OAI

/-! # Whole-atom interval bounds on the actual transfer support

In particular the word atom retains its selected bin, even though its prime
constituents range over a much wider interval.
-/
namespace Ostmann
open scoped Classical BigOperators

theorem constituentTransferWeight_atom_product_bounds {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M a ≠ 0) :
    (∏ h : CopyScheduleH role n, lo (copyScheduleOrigin n h.val)) ≤
      (∏ h, (a.1 h : ℕ)) ∧
    (∏ h, (a.1 h : ℕ)) ≤
      ∏ h : CopyScheduleH role n, hi (copyScheduleOrigin n h.val) := by
  have hf := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound
    (atomIntervalRanges role lo hi) leaf hist u M a hw
  have hr := (atomIntervalRanges_holds_iff role lo hi n _).mp
    (fun r hr => fullAtomTransferWeight_top_range role childBound pivotBound
      (atomIntervalRanges role lo hi) leaf n _ (hist a.2) hf r hr)
  have hh (h : CopyScheduleH role n) :
      lo (copyScheduleOrigin n h.val) ≤
        ∏ k, (a.1 (constituentH role size n h k) : ℕ) ∧
      (∏ k, (a.1 (constituentH role size n h k) : ℕ)) ≤ hi (copyScheduleOrigin n h.val) := by
    simpa only [scheduledInsertedAtoms_H] using hr ⟨h.val, h.property.1⟩
  rw [← constituentH_product role size n (fun h => (a.1 h : ℕ))]
  exact ⟨Finset.prod_le_prod (fun h _ => (hh h).1),
    Finset.prod_le_prod (fun h _ => (hh h).2)⟩

end Ostmann

end OAI
