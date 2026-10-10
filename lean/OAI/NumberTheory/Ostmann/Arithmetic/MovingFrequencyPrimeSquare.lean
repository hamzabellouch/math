import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPrimeExpansion

namespace OAI

/-! # The actual coefficient square inside the original two prime intervals -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- Expanding the square and exchanging the finite prime sums introduces
exactly the two independent descendant histories used in the arithmetic norm. -/
theorem movingFrequencyCoefficient_original_prime_square {σ I : Type} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (u v r w : ℝ) :
    let W := fun (a : MovingDescendantFrequencyIndex V n) (x y : ℝ) =>
      movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
        n (movingRootedFrequencyTree V n s a) small bulk ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
    complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk
        ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ))) =
      ∑ a : MovingDescendantFrequencyIndex V n, ∑ b : MovingDescendantFrequencyIndex V n,
        complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
          W a x y * star (W b x y))) := by
  intro W
  have heq (x y : ℝ) :
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk
        ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ) =
      ∑ a : MovingDescendantFrequencyIndex V n, ∑ b : MovingDescendantFrequencyIndex V n,
        W a x y * star (W b x y) := by
    rw [movingFrequencyCoefficient_original]
    change (‖∑ a, W a x y‖ ^ 2 : ℂ) = _
    calc
      _ = (∑ a, W a x y) * star (∑ b, W b x y) := by
        rw [Complex.star_def, Complex.mul_conj']
      _ = _ := by
        simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
  simp_rw [heq, complexPrimeInterval_sum]

/-- Two descendant histories in a coefficient square share their root.
Their inclusion in the full pair of scheduled histories is injective. -/
def sameRootScheduledPairEmbedding (V : ℕ → ℕ) (n : ℕ) :
    (transferFrequencyRange (V n) ×
      (MovingDescendantFrequencyIndex V n × MovingDescendantFrequencyIndex V n)) ↪
    (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n) where
  toFun a := ((scheduledFrequencyRootEquiv V n).symm (a.1, a.2.1),
    (scheduledFrequencyRootEquiv V n).symm (a.1, a.2.2))
  inj' := by
    intro a b h
    have hl := congrArg (scheduledFrequencyRootEquiv V n) (congrArg Prod.fst h)
    have hr := congrArg (scheduledFrequencyRootEquiv V n) (congrArg Prod.snd h)
    simp only [Equiv.apply_symm_apply] at hl hr
    apply Prod.ext
    · exact congrArg (fun t : transferFrequencyRange (V n) ×
        MovingDescendantFrequencyIndex V n => t.1) hl
    · apply Prod.ext
      · exact congrArg (fun t : transferFrequencyRange (V n) ×
          MovingDescendantFrequencyIndex V n => t.2) hl
      · exact congrArg (fun t : transferFrequencyRange (V n) ×
          MovingDescendantFrequencyIndex V n => t.2) hr

/-- Enlarging only the shared-root restriction costs no factor. This is used
after the exact original prime-pair expansion of each coefficient square. -/
theorem same_root_scheduled_pair_sum_le (V : ℕ → ℕ) (n : ℕ)
    (F : ScheduledFrequencyIndex V n → ScheduledFrequencyIndex V n → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) :
    (∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        F ((scheduledFrequencyRootEquiv V n).symm (s, a))
          ((scheduledFrequencyRootEquiv V n).symm (s, b))) ≤
    ∑ a : ScheduledFrequencyIndex V n, ∑ b : ScheduledFrequencyIndex V n, F a b := by
  let e := sameRootScheduledPairEmbedding V n
  have h : (∑ t ∈ Finset.univ.map e, F t.1 t.2) ≤
      ∑ t : ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n, F t.1 t.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.map e))
    (by intro a _ _; exact hF a.1 a.2)
  rw [Finset.sum_map] at h
  change (∑ a : transferFrequencyRange (V n) ×
    (MovingDescendantFrequencyIndex V n × MovingDescendantFrequencyIndex V n),
    F ((scheduledFrequencyRootEquiv V n).symm (a.1, a.2.1))
      ((scheduledFrequencyRootEquiv V n).symm (a.1, a.2.2))) ≤ _ at h
  simpa only [Fintype.sum_prod_type] using h

end Ostmann

end OAI
