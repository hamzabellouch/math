import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient

namespace OAI

/-! # Only the scheduled bottom frequencies evaluate a leaf multiplier -/
namespace Ostmann
open scoped Classical BigOperators

theorem recursiveTransferWeight_scheduled_leaf_congr {State : Type*}
    (sys : TransferHistorySystem State) (F H : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V : ℕ → ℕ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (n : ℕ) (x : State) (t : ScheduledFrequencyIndex V n) :
    recursiveTransferWeight sys F cutoff n x (scheduledFrequencyHistory V n t) =
      recursiveTransferWeight sys H cutoff n x (scheduledFrequencyHistory V n t) := by
  induction n generalizing x with
  | zero => exact hF x t.val ((mem_transferFrequencyRange _ _).mp t.property)
  | succ n ih =>
    simp only [scheduledFrequencyHistory, recursiveTransferWeight]
    rw [ih _ t.2.1, ih _ t.2.2]

theorem recursiveTransferWeight_rooted_leaf_congr {State : Type*}
    (sys : TransferHistorySystem State) (F H : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V : ℕ → ℕ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n) (x : State)
    (t : MovingDescendantFrequencyIndex V n) :
    recursiveTransferWeight sys F cutoff n x (movingRootedFrequencyTree V n s t) =
      recursiveTransferWeight sys H cutoff n x (movingRootedFrequencyTree V n s t) := by
  let root : transferFrequencyRange (V n) := ⟨s, (mem_transferFrequencyRange _ _).mpr hs⟩
  let d := (scheduledFrequencyRootEquiv V n).symm (root, t)
  have he : scheduledFrequencyHistory V n d = movingRootedFrequencyTree V n s t := by
    rw [scheduledFrequencyRootEquiv_history]
    simp only [d, Equiv.apply_symm_apply, root]
  rw [← he]
  exact recursiveTransferWeight_scheduled_leaf_congr sys F H cutoff V hF n x d

theorem movingFrequencyCoefficient_leaf_congr {P : Type} [Fintype P]
    (value : P → ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F H : MovingSlotState P → ℤ → ℂ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (small bulk : TreeLeafTuple (List P) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small bulk XL XR =
      movingFrequencyCoefficient value outside μ childBound pivotBound V H φ G n s small bulk XL XR := by
  unfold movingFrequencyCoefficient
  apply Finset.sum_congr rfl
  intro t _
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold movingSupportedSampleTerm
  rw [recursiveTransferWeight_rooted_leaf_congr _ F H _ V hF n s hs]

end Ostmann

end OAI
