import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPatternMean

namespace OAI

/-! # The actual coefficient energy as a sum over the original equality patterns -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- The original coefficient square is bounded by the absolute pattern means
with both histories' bottom cutoffs retained. There is no extra root-frequency
or ambient-prime cardinality factor. -/
theorem movingFrequencyCoefficient_original_pattern_bound {σ I B : Type}
    [Fintype σ] [Fintype B]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List B) n) (u v r w : ℝ)
    (hV : Monotone V) (hF : ∀ d (T : MovingSlotData σ d), F T 0 = 0)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
      ∑ x : Fin (N s + 1) → σ,
        movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
          (movingOriginalPatternPrimeObservable (e s) (fun i => Quotient.mk'' i) q value
            outside childBound pivotBound F g Dq S ψ X lo hi φ G
            (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t))
            small bulk u v r w) x
    ‖∑ a : transferFrequencyRange (V n), ∑ z : B → σ, ((∏ b, ν b (z b) : ℝ) : ℂ) *
      complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
        (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
          (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n a.val
          (treeLeafMap (List.map z) n small) (treeLeafMap (List.map z) n bulk)
          ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ)))‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ∑ s : Setoid (Bool × MovingSampleIndex n), ‖term t s‖ := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let M := movingOriginalPrimePairMean q value outside μ childBound pivotBound F g Dq S
    ψ X lo hi φ G n (fun z : B → σ => ∏ b, ν b (z b))
    (fun z => treeLeafMap (List.map z) n small)
    (fun z => treeLeafMap (List.map z) n bulk) u v r w
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
  have hs := same_root_scheduled_pair_sum_le V n
    (fun a b => ‖M (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)‖)
    (fun _ _ => norm_nonneg _)
  have hh (a : transferFrequencyRange (V n)) (b : MovingDescendantFrequencyIndex V n) :
      scheduledFrequencyHistory V n ((scheduledFrequencyRootEquiv V n).symm (a, b)) =
        movingRootedFrequencyTree V n a.val b := by
    rw [scheduledFrequencyRootEquiv_history, Equiv.apply_symm_apply]
  simp_rw [hh] at hs
  have he := paired_scheduled_history_sum_le V hV n (fun a b => ‖M a b‖)
    (fun _ _ => norm_nonneg _) (fun a t ha => by rw [hzL a t ha, norm_zero])
    (fun t a ha => by rw [hzR t a ha, norm_zero])
  rw [movingFrequencyCoefficient_original_mean_square q value outside μ childBound pivotBound V
    F g Dq S ψ X lo hi φ G n (fun z : B → σ => ∏ b, ν b (z b))
    (fun z => treeLeafMap (List.map z) n small) (fun z => treeLeafMap (List.map z) n bulk) u v r w]
  apply le_trans _ (hs.trans (he.trans ?_))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    exact norm_sum_le _ _
  · apply Finset.sum_le_sum
    intro t _
    have hpatterns := movingOriginalPrimePairMean_patterns q value outside μ ν childBound
      pivotBound F g Dq S ψ X lo hi φ G n
      (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t))
      small bulk u v r w N e
    change M _ _ = _ at hpatterns
    split_ifs
    · rw [hpatterns]
      exact norm_sum_le _ _
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

end Ostmann

end OAI
