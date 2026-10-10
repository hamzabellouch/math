import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedMatchedCorrelation

namespace OAI

/-! # The original paired frequency histories with the exterior multiplier retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedCorrelation_history_bound {B : Type} [Fintype B]
    (primes : Finset ℕ) (outside : List ℕ)
    (n m : ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : ℤ → (B → primes) → ℝ → ℝ → ℂ)
    (u v r w center : ℝ) (hV : Monotone V) :
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    ‖movingWeightedMatchedCorrelation p Subtype.val outside μ ν childBound pivotBound V f g Dq
      Finset.univ ψ X lo hi φ G n small bulk W u v r w center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n,
        ‖movingWeightedMatchedMean p Subtype.val outside μ ν childBound pivotBound f g Dq
          Finset.univ ψ X lo hi φ G n (trees t) small bulk
          (W (frequencyRoot n (trees t false))) u v r w center‖ := by
  dsimp only
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let M := fun a b : FrequencyTree ℤ n =>
    movingWeightedMatchedMean p (fun q : primes => (q : ℕ)) outside μ ν childBound pivotBound
      f g Dq Finset.univ ψ X lo hi φ G n (fun side => if side then b else a)
      small bulk (W (frequencyRoot n a)) u v r w center
  have hzL (a : ScheduledFrequencyIndex V n) (t : FrequencyTree ℤ n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M (scheduledFrequencyHistory V n a) t = 0 :=
    movingWeightedMatchedMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      bulk (W _) u v r w center false ha
  have hzR (t : FrequencyTree ℤ n) (a : ScheduledFrequencyIndex V n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M t (scheduledFrequencyHistory V n a) = 0 :=
    movingWeightedMatchedMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      bulk (W _) u v r w center true ha
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
  rw [movingWeightedMatchedCorrelation_eq]
  apply le_trans _ (hs.trans (he.trans ?_))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    have hb := norm_sum_le (Finset.univ : Finset (MovingDescendantFrequencyIndex V n))
      (fun c => movingWeightedMatchedMean p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G n
        (fun side => if side then movingRootedFrequencyTree V n a.val c
          else movingRootedFrequencyTree V n a.val b)
        small bulk (W a.val) u v r w center)
    simpa only [M, frequencyRoot_movingRootedFrequencyTree] using hb
  · apply Finset.sum_le_sum
    intro t _
    let trees := fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    have htrees : (fun side => if side then trees true else trees false) = trees := by
      funext side
      cases side <;> rfl
    dsimp only [M]
    rw [htrees]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _

end Ostmann

end OAI
