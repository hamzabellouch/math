import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogProduct

namespace OAI

/-! # Removing a bulk cutoff only from one-branch coefficient energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateCoefficient_bulk_log_norm_le {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (hn : n ≤ k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (XL XR : ℕ) :
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n r m s y XL XR‖ ≤
      ‖movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n r m s y XL XR‖ := by
  have hs : ∀ i ∈ flattenMovingSlots n
      (treeLeafMap (List.map y) n (movingTemplateSmall n r m)), tier i ≠ k := by
    intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ a).mp ha
    exact hsmall j
  have hb : ∀ i ∈ flattenMovingSlots n
      (treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m))), tier i = k := by
    intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m _ a).mp ha
    exact hbulk j
  exact movingFrequencyCoefficient_bulk_log_norm_le value tier k outside cb cd μ hμ
    childBound pivotBound V F φ G n s _ _ hn hs hb XL XR

/-- The compensation factors are restored before applying the one-branch
norm inequality. This does not assert domination of a signed pair average. -/
theorem movingTemplateCoefficient_restored_bulk_log_norm_le {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (y : MovingRegularSlot n r m → σ) (hn : n < k)
    (hsmall : ∀ j : TreeLeafIndex n × Fin r, tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ j : TreeLeafIndex n × Fin m, tier (y (j.1, .inr j.2)) = k)
    (XL XR : ℕ) :
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n (4 + r) m s (movingRestoreSample n r m u y) XL XR‖ ≤
      ‖movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s (movingRestoreSample n r m u y) XL XR‖ := by
  have hut i : tier (u i) = n :=
    hμ n (u i) ((Finset.prod_ne_zero_iff.mp hu) i (Finset.mem_univ i))
  apply movingTemplateCoefficient_bulk_log_norm_le value tier k outside cb cd μ hμ
    childBound pivotBound V F φ G n (4 + r) m s _ hn.le _ _ XL XR
  · rintro ⟨j, i⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · dsimp only
      rw [movingRestoreSample_compensation n r m u y (j, i), hut]
      exact hn.ne
    · dsimp only
      rw [movingRestoreSample_small]
      exact hsmall (j, i)
  · intro j
    change tier (movingRestoreSample n r m u y (movingTemplateBulk n (4 + r) m j)) = k
    rw [movingRestoreSample_bulk]
    exact hbulk j

end Ostmann

end OAI
