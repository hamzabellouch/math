import OAI.NumberTheory.Ostmann.Construction.SelectedBulkSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullHarmonicCost

namespace OAI

/-! # The full harmonic denominator survives bulk symmetrization -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSymmetrizedTemplateCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (y : MovingRegularSlot n r m → σ)
    (XL XR : ℕ) : ℂ :=
  mixedBulkSymmetrize n m (movingTemplateBulk n r m)
    (fun _ z _ _ => movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
      n (4 + r) m s (movingRestoreSample n r m u z) XL XR) 0 y 0 0

theorem selectedBulkSample_prod {B J A M : Type*} [Fintype B] [CommMonoid M]
    (slot : J ↪ B) (e : Equiv.Perm J) (value : A → M) (y : B → A) :
    (∏ i, value (selectedBulkSample slot e y i)) = ∏ i, value (y i) := by
  exact (selectedBulkPerm slot e).symm.prod_comp (fun i => value (y i))

theorem movingSymmetrizedTemplateCoefficient_full_product_lower {σ : Type} [Fintype σ]
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
    (XL XR : ℕ)
    (h : movingSymmetrizedTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n r m s u y XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1)) ≤
      ((∏ i, value (y i) : ℕ) : ℝ) := by
  obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n m (movingTemplateBulk n r m) _ 0 y 0 0 h
  have hs (j : TreeLeafIndex n × Fin r) :
      tier (selectedBulkSample (movingTemplateBulk n r m) e y (j.1, .inl j.2)) ≠ k := by
    rw [selectedBulkSample_template_small]
    exact hsmall j
  have hb (j : TreeLeafIndex n × Fin m) :
      tier (selectedBulkSample (movingTemplateBulk n r m) e y (j.1, .inr j.2)) = k := by
    change tier (selectedBulkSample (movingTemplateBulk n r m) e y
      (movingTemplateBulk n r m j)) = k
    rw [selectedBulkSample_bulk]
    exact hbulk (e.symm j)
  have hl (j : TreeLeafIndex n × Fin r) :
      Real.exp (lower j) ≤
        (value (selectedBulkSample (movingTemplateBulk n r m) e y (j.1, .inl j.2)) : ℝ) := by
    rw [selectedBulkSample_template_small]
    exact hlower j
  have hp := movingTemplateCoefficient_restored_full_product_lower value tier hvalue k outside cb cd
    μ hμ childBound pivotBound V F φ G n r m s u hu
    (selectedBulkSample (movingTemplateBulk n r m) e y) hn hs hb lower hl XL XR he
  rwa [selectedBulkSample_prod] at hp

theorem movingSymmetrizedTemplateCoefficient_full_harmonic_cost_le {σ : Type} [Fintype σ]
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
    (h : movingSymmetrizedTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n r m s u y XL XR ≠ 0) :
    (Real.exp cg / XR) * ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) * ((∏ i, value (y i) : ℕ) : ℝ)⁻¹ ≤
      Real.exp (cg - Gmin - ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1))) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
          (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹) := by
  exact moving_harmonic_full_counterpart_le n r m Q cg Gmin
    ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1)) XR (value ∘ y) hX
    (movingSymmetrizedTemplateCoefficient_full_product_lower value tier hvalue k outside cb cd μ hμ
      childBound pivotBound V F φ G n r m s u hu y hn hsmall hbulk lower hlower XL XR h)

end Ostmann

end OAI
