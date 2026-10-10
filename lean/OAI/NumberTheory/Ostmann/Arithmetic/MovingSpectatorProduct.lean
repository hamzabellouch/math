import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullSpectator

namespace OAI

/-! # All spectator factors in the source recursive coefficient -/

namespace Ostmann
open scoped BigOperators Classical

/-- Factor every spectator while retaining the full smooth and arithmetic
coefficient. This identity includes zero-support terms. -/
theorem movingSlotWeight_spectator_product {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ i x s v w, extra x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod (q i)) ≠ 0)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        ∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR := by
  induction S using Finset.induction_on generalizing F with
  | empty => simp only [Finset.prod_empty, mul_one]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    have he : (fun x s => F x s * (spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s *
        ∏ j ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g j) (D j) x s)) =
        (fun x s => (F x s * ∏ j ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g j) (D j) x s) *
          spectatorHistoryLeaf (movingSlotModulus value) (g i) (D i) x s) := by
      funext x s
      ring
    rw [he, movingSlotWeight_spectator value childBound pivotBound _ extra (hextra i)
      (g i) (D i) T t hT XL XR, ih]
    ring

end Ostmann

end OAI
