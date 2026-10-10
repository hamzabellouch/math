import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicCounterpart
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmallProductLower

namespace OAI

/-! # The counterpart cost retaining every actual small-cell endpoint -/

namespace Ostmann
open scoped Classical BigOperators

theorem moving_harmonic_full_counterpart_le (n r m : ℕ)
    (Q : MovingRegularSlot n r m → Finset ℕ) (cg Gmin totalLower : ℝ)
    (X : ℕ) (y : MovingRegularSlot n r m → ℕ)
    (hX : Real.exp Gmin ≤ (X : ℝ))
    (hy : Real.exp (totalLower) ≤ ((∏ i, y i : ℕ) : ℝ)) :
    (Real.exp cg / X) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, y i : ℕ) : ℝ)⁻¹ ≤
      Real.exp (cg - Gmin - totalLower) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
          (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) := by
  let K := ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
    (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
      (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q)))))
  have hp : 0 < Real.exp Gmin * Real.exp (totalLower) := by positivity
  have hden : Real.exp Gmin * Real.exp (totalLower) ≤
      (X : ℝ) * ((∏ i, y i : ℕ) : ℝ) :=
    mul_le_mul hX hy (Real.exp_nonneg _) (Nat.cast_nonneg _)
  calc
    _ = (Real.exp cg / ((X : ℝ) * ((∏ i, y i : ℕ) : ℝ))) * K := by
      dsimp only [K]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (Real.exp cg / (Real.exp Gmin * Real.exp (totalLower))) * K :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (Real.exp_nonneg _) hp hden) hK
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_sub]
      rw [show cg - (Gmin + totalLower) =
        cg - Gmin - totalLower by ring]
      dsimp only [K]
      ring

/-- Both the small-cell endpoints and the terminal bulk bin remain in the
same denominator, so the compensation cost can cancel against their sum. -/
theorem movingTemplate_restored_full_harmonic_cost_le {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (y : MovingRegularSlot n r m → σ) (hn : n < k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ))
    (XL XR : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ) (cg Gmin : ℝ)
    (hX : Real.exp Gmin ≤ (XR : ℝ))
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n (4 + r) m s (movingRestoreSample n r m u y) XL XR ≠ 0) :
    (Real.exp cg / XR) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, value (y i) : ℕ) : ℝ)⁻¹ ≤
      Real.exp (cg - Gmin - ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1))) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
          (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) := by
  exact moving_harmonic_full_counterpart_le n r m Q cg Gmin
    ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1)) XR (value ∘ y) hX
    (movingTemplateCoefficient_restored_full_product_lower value tier hvalue k outside cb cd μ hμ
      childBound pivotBound V F φ G n r m s u hu y hn hsmall hbulk lower hlower XL XR h)

end Ostmann

end OAI
