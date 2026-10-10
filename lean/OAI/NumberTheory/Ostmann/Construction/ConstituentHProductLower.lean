import OAI.NumberTheory.Ostmann.Construction.FullAtomProductBounds

namespace OAI

/-! # A lower endpoint for the actual supported H product -/
namespace Ostmann
open scoped Classical BigOperators

/-- The endpoint is required only where the full inherited coefficient is live. -/
def ConstituentHProductLower {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (Z : ℝ) : Prop :=
  ∀ (M : ℕ) (t : FrequencyTree ℤ n)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ),
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t ≠ 0 →
      Z ≤ ∏ h, (l h : ℝ)

theorem constituentHProductLower_of_atom_intervals {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (lo hi : I → ℕ)
    (leaf : ScheduleAtomState role → ℤ → ℂ) (Z : ℝ)
    (hZ : Z ≤ ∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ)) :
    ConstituentHProductLower role size n childBound pivotBound
      (atomIntervalRanges role lo hi) leaf Z := by
  intro M t l u hw
  apply hZ.trans
  exact_mod_cast (fullAtomTransferWeight_inserted_H_product_bounds role size n
    childBound pivotBound lo hi leaf t l u M hw).1

end Ostmann

end OAI
