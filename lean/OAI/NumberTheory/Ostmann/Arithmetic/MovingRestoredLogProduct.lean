import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogProduct

namespace OAI

/-! # The bulk lower cutoff survives restoration of compensation coordinates -/

namespace Ostmann
open scoped Classical BigOperators

/-- Restoring the independent compensation draw does not charge its product
to the lower bound for the surviving regular modulus. -/
theorem movingTemplateCoefficient_restored_log_product_lower {σ : Type} [Fintype σ]
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
    Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ i, value (y i) : ℕ) : ℝ) := by
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
  have heq : (∏ j : TreeLeafIndex n × Fin m,
      value (movingRestoreSample n r m u y (j.1, .inr j.2))) =
      ∏ j : TreeLeafIndex n × Fin m, value (y (j.1, .inr j.2)) := by
    apply Finset.prod_congr rfl
    intro j _
    change value (movingRestoreSample n r m u y (movingTemplateBulk n (4 + r) m j)) = _
    rw [movingRestoreSample_bulk]
    rfl
  rw [heq] at hlow
  apply hlow.trans
  have hsmallprod : 1 ≤ ∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2)) :=
    Finset.one_le_prod (fun j _ => hvalue _)
  have he : (∏ i, value (y i)) =
      (∏ j : TreeLeafIndex n × Fin r, value (y (j.1, .inl j.2))) *
      (∏ j : TreeLeafIndex n × Fin m, value (y (j.1, .inr j.2))) := by
    simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
      Finset.prod_mul_distrib]
  rw [he]
  exact_mod_cast le_mul_of_one_le_left (Nat.zero_le _) hsmallprod

end Ostmann

end OAI
