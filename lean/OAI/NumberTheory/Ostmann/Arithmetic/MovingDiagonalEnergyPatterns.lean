import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalEnergy

namespace OAI

/-! # The complete diagonal energy is controlled by its signed pattern means -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalDiagonalEnergy_pattern_bound {B : Type} [Fintype B]
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (outside : List ℕ)
    (n m : ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) (hV : Monotone V)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
      ∑ x : Fin (N s + 1) → primes,
        movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n
          (fun i => Quotient.mk'' i)
          (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot (fun i => Quotient.mk'' i)
            primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get
            (fun _ => true) (frequencyRoot n (trees t false))
            (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
              (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
            ψ X lo hi φ G Jleft Jright diagonal u v r w center) x
    ‖movingOriginalDiagonalEnergy p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound V f g Dq Finset.univ ψ X lo hi φ G n small
      (bulkSlotLeaves n m slot) greg Jleft Jright diagonal u v r w center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ∑ s : Setoid (Bool × MovingSampleIndex n), ‖term t s‖ := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let M := fun a b : FrequencyTree ℤ n =>
    movingOriginalDiagonalMean p (fun q : primes => (q : ℕ)) outside μ ν childBound pivotBound
      f g Dq Finset.univ ψ X lo hi φ G n (fun side => if side then b else a)
      small (bulkSlotLeaves n m slot) greg (frequencyRoot n a) Jleft Jright diagonal u v r w center
  have hzL (a : ScheduledFrequencyIndex V n) (t : FrequencyTree ℤ n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M (scheduledFrequencyHistory V n a) t = 0 :=
    movingOriginalDiagonalMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      (bulkSlotLeaves n m slot) greg _ Jleft Jright diagonal u v r w center false ha
  have hzR (t : FrequencyTree ℤ n) (a : ScheduledFrequencyIndex V n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M t (scheduledFrequencyHistory V n a) = 0 :=
    movingOriginalDiagonalMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      (bulkSlotLeaves n m slot) greg _ Jleft Jright diagonal u v r w center true ha
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
  rw [movingOriginalDiagonalEnergy_eq]
  apply le_trans _ (hs.trans (he.trans ?_))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    have hb := norm_sum_le (Finset.univ : Finset (MovingDescendantFrequencyIndex V n))
      (fun c => movingOriginalDiagonalMean p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G n
        (fun side => if side then movingRootedFrequencyTree V n a.val c
          else movingRootedFrequencyTree V n a.val b)
        small (bulkSlotLeaves n m slot) greg a.val Jleft Jright diagonal u v r w center)
    simpa only [M, frequencyRoot_movingRootedFrequencyTree] using hb
  · apply Finset.sum_le_sum
    intro t _
    let trees := fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    have hpatterns := movingOriginalDiagonalMean_finite_patterns trees small slot primes hprimes
      p μ ν g Dq greg (frequencyRoot n (trees false)) f outside childBound pivotBound
      ψ X lo hi φ G Jleft Jright diagonal u v r w center N e
    have htrees : (fun side => if side then trees true else trees false) = trees := by
      funext side
      cases side <;> rfl
    dsimp only at hpatterns
    conv_lhs at hpatterns => rw [← htrees]
    change M (trees false) (trees true) = _ at hpatterns
    split_ifs
    · rw [hpatterns]
      exact norm_sum_le _ _
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

end Ostmann

end OAI
