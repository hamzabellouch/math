import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredLogProduct

namespace OAI

/-! # Retaining the actual small-cell contribution to the regular modulus -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_small_product_lower {A : Type*} (value : A → ℕ)
    (n r m : ℕ) (y : MovingRegularSlot n r m → A)
    (lower : TreeLeafIndex n × Fin r → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) :
    Real.exp (∑ j, lower j) ≤
      ((∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2)) : ℕ) : ℝ) := by
  rw [Real.exp_sum, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun j _ => Real.exp_nonneg _) (fun j _ => hlower j)

theorem movingTemplateCoefficient_restored_bulk_product_lower {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (y : MovingRegularSlot n r m → σ) (hn : n < k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n (4 + r) m s (movingRestoreSample n r m u y) XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤
      ((∏ j : TreeLeafIndex n × Fin m, value (y (j.1, .inr j.2)) : ℕ) : ℝ) := by
  have hut i : tier (u i) = n :=
    hμ n (u i) ((Finset.prod_ne_zero_iff.mp hu) i (Finset.mem_univ i))
  have hs : ∀ j : TreeLeafIndex n × Fin (4 + r),
      tier (movingRestoreSample n r m u y (j.1, .inl j.2)) ≠ k := by
    rintro ⟨j, i⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · dsimp only
      rw [movingRestoreSample_compensation n r m u y (j, i), hut]
      exact hn.ne
    · dsimp only
      rw [movingRestoreSample_small]
      exact hsmall (j, i)
  have hb : ∀ j : TreeLeafIndex n × Fin m,
      tier (movingRestoreSample n r m u y (j.1, .inr j.2)) = k := by
    intro j
    change tier (movingRestoreSample n r m u y (movingTemplateBulk n (4 + r) m j)) = k
    rw [movingRestoreSample_bulk]
    exact hbulk j
  have hlow := movingTemplateCoefficient_bulk_log_product_lower value tier hvalue k outside cb cd
    μ hμ childBound pivotBound V F φ G n (4 + r) m s (movingRestoreSample n r m u y)
    hn.le hs hb XL XR h
  convert hlow using 1
  congr 2

theorem movingTemplateCoefficient_restored_full_product_lower {σ : Type} [Fintype σ]
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
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n (4 + r) m s (movingRestoreSample n r m u y) XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ i, value (y i) : ℕ) : ℝ) := by
  have hs := movingTemplate_small_product_lower value n r m y lower hlower
  have hb := movingTemplateCoefficient_restored_bulk_product_lower value tier hvalue k outside cb cd
    μ hμ childBound pivotBound V F φ G n r m s u hu y hn hsmall hbulk XL XR h
  rw [Real.exp_add]
  convert mul_le_mul hs hb (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
  rw [← Nat.cast_mul]
  congr 1
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Finset.prod_mul_distrib]

end Ostmann

end OAI
