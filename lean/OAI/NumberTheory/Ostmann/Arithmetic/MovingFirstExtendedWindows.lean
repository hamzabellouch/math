import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialCoefficient

namespace OAI

/-! # Both terminal windows survive extension of the outer giants to integers -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- A nonzero first node contains a nonzero pair of terminal coefficients, even
when either outer giant has been extended to a positive integer. All original
cross-branch support tests stay inside the selected summand. -/
theorem movingFrequencyCoefficient_one_extended_children {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ)
    (small bulk : List σ × List σ) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      1 s small bulk XL XR ≠ 0) :
    ∃ (a : Fin 4 → σ) (v w : transferFrequencyRange (V 0)),
      let u := List.ofFn a
      let p := movingTopPivot value (small.1 ++ bulk.1) (small.2 ++ bulk.2)
        u XL XR s v.val w.val
      movingCompensationPrior (μ 0) 0 a ≠ 0 ∧ 0 < p ∧
      0 < MovingSlotReversal.naturalProduct value u ∧
      φ (Real.log p - G 1) ≠ 0 ∧
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 v.val
        (u ++ small.1) bulk.1 p XL ≠ 0 ∧
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 w.val
        (u ++ small.2) bulk.2 p XR ≠ 0 := by
  rw [movingFrequencyCoefficient_node value outside μ childBound pivotBound V F φ G
    0 s small bulk XL XR] at h
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  dsimp only at ha
  have hm : movingCompensationPrior (μ 0) 0 a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, Complex.ofReal_zero, zero_mul])
  have hb := right_ne_zero_of_mul ha
  split_ifs at hb with hg
  · have hpos := hg.2.1.pivot_pos
    have hp : 0 < movingTopPivot value (small.1 ++ bulk.1) (small.2 ++ bulk.2)
        (List.ofFn a) XL XR s v.val w.val := Nat.pos_of_mul_pos_right hpos
    have hphi : φ (Real.log (movingTopPivot value (small.1 ++ bulk.1)
        (small.2 ++ bulk.2) (List.ofFn a) XL XR s v.val w.val) - G 1) ≠ 0 := by
      intro hz
      apply left_ne_zero_of_mul (left_ne_zero_of_mul hb)
      change (((MovingSlotReversal.naturalProduct value (List.ofFn a) : ℝ) *
        φ (Real.log (movingTopPivot value (small.1 ++ bulk.1) (small.2 ++ bulk.2)
          (List.ofFn a) XL XR s v.val w.val) - G 1) : ℝ) : ℂ) = 0
      rw [hz, mul_zero, Complex.ofReal_zero]
    refine ⟨a, v, w, hm, hp, hg.2.2, hphi, ?_, ?_⟩
    · rw [movingFrequencyCoefficient_levelZero_sample]
      exact right_ne_zero_of_mul (left_ne_zero_of_mul hb)
    · rw [movingFrequencyCoefficient_levelZero_sample]
      exact star_ne_zero.mp (right_ne_zero_of_mul hb)
  · exact (hb rfl).elim

end Ostmann

end OAI
