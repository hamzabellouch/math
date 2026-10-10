import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredLogProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingHarmonicCounterpart

namespace OAI

/-! # The harmonic counterpart cost on the original restored support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_restored_harmonic_cost_le {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (y : MovingRegularSlot n r m → σ) (hn : n < k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (XL XR : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ) (cg Gmin : ℝ)
    (hX : Real.exp Gmin ≤ (XR : ℝ))
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n (4 + r) m s (movingRestoreSample n r m u y) XL XR ≠ 0) :
    (Real.exp cg / XR) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, value (y i) : ℕ) : ℝ)⁻¹ ≤
      Real.exp (cg - Gmin - (2 ^ n : ℕ) * (cb - 1)) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
          (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) := by
  exact moving_harmonic_counterpart_le n r m Q cg Gmin cb XR (value ∘ y) hX
    (movingTemplateCoefficient_restored_log_product_lower value tier hvalue k outside cb cd μ hμ
      childBound pivotBound V F φ G n r m s u hu y hn hsmall hbulk XL XR h)

end Ostmann

end OAI
