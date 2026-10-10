import OAI.NumberTheory.Ostmann.Arithmetic.MovingSymmetrizedMaskedKernel

namespace OAI

/-! # The bulk-averaged masked energy under the original restored prior -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSymmetrizedMaskedTemplateEnergy
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (weight : (MovingRegularSlot n (4 + r) m → P) → ℝ) : ℝ :=
  ∑ x : MovingRegularSlot n (4 + r) m → P,
    (∏ i, movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)) i (x i)) *
      (weight x * ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
        ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
          ∑ s : transferFrequencyRange (V n),
            movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m
              greg x p X s.val)

theorem movingSymmetrizedMaskedTemplateKernel_nonneg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (x : MovingRegularSlot n (4 + r) m → P) (p X : ℕ) (s : ℤ) :
    0 ≤ movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg x p X s := by
  unfold movingSymmetrizedMaskedTemplateKernel
  dsimp only
  apply mul_nonneg (sq_nonneg _)
  unfold naturalRegularMultiplier
  apply Finset.prod_nonneg
  intro i _
  split <;> positivity

/-- A bound on the original support suffices: no support is conditioned into
or removed from the independent restored law. -/
theorem movingSymmetrizedMaskedTemplateEnergy_weight_le
    (P Pg I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t) (G : ℕ → ℝ) (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (weight : (MovingRegularSlot n (4 + r) m → P) → ℝ) (B : ℝ)
    (hweight : ∀ x, (∏ i, movingTemplateRestoredPrior n r m (μ n)
      (fun i => primeSubsetPrior P (Q i)) i (x i)) ≠ 0 → weight x ≤ B) :
    movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg weight ≤
      B * movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G n r m Q greg (fun _ => 1) := by
  unfold movingSymmetrizedMaskedTemplateEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  let mass := ∏ i, movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i)) i (x i)
  have hm : 0 ≤ mass := by
    apply Finset.prod_nonneg
    intro i _
    unfold movingTemplateRestoredPrior
    cases he : (movingReverseTemplate n r m).symm i with
    | inl j => exact hμ n (x i)
    | inr j => exact primeSubsetPrior_nonneg P (Q j) (x i)
  by_cases hz : mass = 0
  · change mass * _ ≤ B * (mass * _)
    simp only [hz, zero_mul, mul_zero, le_refl]
  have hE : 0 ≤ ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      ∑ X : Pg, smoothGiantPrior Pg φ (G (n + 1)) X *
        ∑ s : transferFrequencyRange (V n),
          movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G n r m greg x p X s.val := by
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg (hφ _)
    apply Finset.sum_nonneg
    intro X _
    apply mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ X)
    exact Finset.sum_nonneg (fun s _ => movingSymmetrizedMaskedTemplateKernel_nonneg P hP outside μ
      childBound pivotBound V F φ G n r m greg x p X s.val)
  have ht := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hweight x hz) hE) hm
  convert ht using 1
  ring

end Ostmann

end OAI
