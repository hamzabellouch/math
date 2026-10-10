import OAI.NumberTheory.Ostmann.ZeroDensity.MovingZeroFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.PairedScheduledNormBound

namespace OAI

/-! # The original coefficient square and the scheduled arithmetic budget -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The original external average of two sampled histories. The external
weights may in particular be the unchanged product of harmonic prime priors. -/
noncomputable def movingOriginalPrimePairMean {σ I Ω : Type}
    [Fintype σ] [Fintype Ω] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (ν : Ω → ℝ) (small bulk : Ω → TreeLeafTuple (List σ) n)
    (u v r w : ℝ) (l h : FrequencyTree ℤ n) : ℂ :=
  ∑ z, (ν z : ℂ) * complexPrimeInterval 1 0 r w (fun y =>
    complexPrimeInterval 1 0 u v (fun x =>
      movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi
        φ G n l (small z) (bulk z) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
      star (movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi
        φ G n h (small z) (bulk z) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)))

section
variable {σ I Ω : Type} [Fintype σ] [Fintype Ω]
  (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
  (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
  (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
  (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
  (n : ℕ) (ν : Ω → ℝ) (small bulk : Ω → TreeLeafTuple (List σ) n)
  (u v r w : ℝ)

theorem movingFrequencyCoefficient_original_mean_square :
    (∑ s : transferFrequencyRange (V n), ∑ z, (ν z : ℂ) *
      complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
        (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
          (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s.val
          (small z) (bulk z) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ)))) =
    ∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        movingOriginalPrimePairMean q value outside μ childBound pivotBound F g Dq S ψ X lo hi
          φ G n ν small bulk u v r w
          (movingRootedFrequencyTree V n s.val a) (movingRootedFrequencyTree V n s.val b) := by
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [movingFrequencyCoefficient_original_prime_square, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

/-- This uses the actual two-history mean and the exact coefficient-square
identity. Only the negligible error receives the full history count. -/
theorem movingFrequencyCoefficient_original_arithmetic_budget
    (hV : Monotone V) (hF : ∀ d (T : MovingSlotData σ d), F T 0 = 0)
    (D K err : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hdiv : ∀ a : ℕ, a ≠ 0 → a ≤ V n ^ 2 → (a.divisors.card : ℝ) ≤ D) :
    let M := movingOriginalPrimePairMean q value outside μ childBound pivotBound F g Dq S
      ψ X lo hi φ G n ν small bulk u v r w
    (∀ t : FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
        ((transferFrequencyRange (V n)).erase 0)) n,
      ‖M (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n false t))
        (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n true t))‖ ≤
      err + K * (frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
        (V 0)) n t * ((frequencySplitList ((transferFrequencyRange (V n)).erase 0) n t).map
          (pairFrequencySupportBound D)).prod)) →
    ‖∑ s : transferFrequencyRange (V n), ∑ z, (ν z : ℂ) *
      complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
        (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
          (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s.val
          (small z) (bulk z) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ)))‖ ≤
      (Fintype.card (FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
        ((transferFrequencyRange (V n)).erase 0)) n) : ℝ) * err +
        K * ((8 * D ^ 4 * (1 + Real.log (V n)) ^ 3) ^ (2 ^ n - 1) *
          (2 * (V 0 : ℝ)) ^ (2 * 2 ^ n)) := by
  intro M hpoint
  have hzL (a : ScheduledFrequencyIndex V n) (t : FrequencyTree ℤ n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M (scheduledFrequencyHistory V n a) t = 0 := by
    dsimp only [M, movingOriginalPrimePairMean]
    simp_rw [movingOriginalSampleAverage_zero_frequency q value outside μ childBound pivotBound
      F hF g Dq S ψ X lo hi φ G n _ _ _ _ _ ha, zero_mul]
    simp only [complexPrimeInterval, zero_mul, ite_self, Finset.sum_const_zero, mul_zero]
  have hzR (t : FrequencyTree ℤ n) (a : ScheduledFrequencyIndex V n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M t (scheduledFrequencyHistory V n a) = 0 := by
    dsimp only [M, movingOriginalPrimePairMean]
    simp_rw [movingOriginalSampleAverage_zero_frequency q value outside μ childBound pivotBound
      F hF g Dq S ψ X lo hi φ G n _ _ _ _ _ ha, star_zero, mul_zero]
    simp only [complexPrimeInterval, zero_mul, ite_self, Finset.sum_const_zero, mul_zero]
  have hb := paired_scheduled_frequency_budget V hV n D K err hD hK hdiv
    (fun a b => ‖M a b‖) (fun _ _ => norm_nonneg _)
    (fun a t ha => by rw [hzL a t ha, norm_zero])
    (fun t a ha => by rw [hzR t a ha, norm_zero]) hpoint
  rw [movingFrequencyCoefficient_original_mean_square q value outside μ childBound pivotBound V
    F g Dq S ψ X lo hi φ G n ν small bulk u v r w]
  have hs := same_root_scheduled_pair_sum_le V n
    (fun a b => ‖M (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)‖)
    (fun _ _ => norm_nonneg _)
  have hh (s : transferFrequencyRange (V n)) (a : MovingDescendantFrequencyIndex V n) :
      scheduledFrequencyHistory V n ((scheduledFrequencyRootEquiv V n).symm (s, a)) =
        movingRootedFrequencyTree V n s.val a := by
    rw [scheduledFrequencyRootEquiv_history, Equiv.apply_symm_apply]
  simp_rw [hh] at hs
  apply le_trans _ (hs.trans hb)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  exact norm_sum_le _ _

end
end Ostmann

end OAI
