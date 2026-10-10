import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogProductLower
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient

namespace OAI

/-! # The bulk cutoff bounds the full restored regular modulus -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original weighted coefficient forces the full bulk product above
its log-bin boundary before any compensation product is included. -/
theorem movingTemplateCoefficient_bulk_log_product_lower {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (hn : n ≤ k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n r m s y XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ j : TreeLeafIndex n × Fin m, value (y (j.1, .inr j.2)) : ℕ) : ℝ) := by
  have hs : ∀ i ∈ flattenMovingSlots n
      (treeLeafMap (List.map y) n (movingTemplateSmall n r m)), tier i ≠ k := by
    intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ a).mp ha
    exact hsmall j
  have hb : ∀ i ∈ flattenMovingSlots n
      (bulkSlotLeaves n m (y ∘ movingTemplateBulk n r m)), tier i = k := by
    intro i hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m _ i).mp hi
    exact hbulk j
  unfold movingTemplateCoefficient at h
  rw [bulkSlotLeaves_map] at h
  have hlow := movingFrequencyCoefficient_log_product_lower value tier hvalue k outside cb cd μ hμ
    childBound pivotBound V F φ G n m s _ (y ∘ movingTemplateBulk n r m) hn hs hb XL XR h
  exact hlow

/-- The original weighted coefficient forces the full bulk product above
its log-bin boundary. Small-slot primes only increase the regular modulus. -/
theorem movingTemplateCoefficient_log_product_lower {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (hn : n ≤ k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n r m s y XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ i, value (y i) : ℕ) : ℝ) := by
  have hlow := movingTemplateCoefficient_bulk_log_product_lower value tier hvalue k outside cb cd
    μ hμ childBound pivotBound V F φ G n r m s y hn hsmall hbulk XL XR h
  have hsmallprod : 1 ≤ ∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2)) :=
    Finset.one_le_prod (fun j _ => hvalue _)
  have he : (∏ i, value (y i)) =
      (∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2))) *
      (∏ j : TreeLeafIndex n × Fin m, value (y (j.1, .inr j.2))) := by
    simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
      Finset.prod_mul_distrib]
  apply hlow.trans
  rw [he]
  exact_mod_cast le_mul_of_one_le_left (Nat.zero_le _) hsmallprod

end Ostmann

end OAI
