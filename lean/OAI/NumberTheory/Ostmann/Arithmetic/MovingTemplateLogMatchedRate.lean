import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogMatchedBound
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticGoodPatternRate

namespace OAI

/-! # Full original matched correlation from the signed pattern budget -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateLogMatchedCorrelation_pattern_rate
    (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k)
    (Cfreq Cprior gain : ℝ) (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
        ∀ (r₀ : ℕ)
          (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
          (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
          (μ : ℕ → primes → ℝ) (ν : MovingRegularSlot n r₀ m → primes → ℝ)
          (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
          (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
          (X Δ hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
          (active : MovingRegularSlot n r₀ m → Bool)
          (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
          (greg : ∀ q : ℕ, ZMod q → ℂ) (outside : List ℕ)
          (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center cb : ℝ)
          (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
          (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ MovingRegularSlot n r₀ m ⊕ Quotient s),
        let small := movingTemplateSmall n r₀ m
        let slot := movingTemplateBulk n r₀ m
        let logSlots := movingBulkPairedCutoffSlots n (movingPatternBulkLeaves n m slot perm)
        let wgt := fun (y : MovingRegularSlot n r₀ m → primes) =>
          ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let Sfreq := (transferFrequencyRange (V n)).erase 0
        let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
          frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
        let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
        let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
          ∑ x : Fin (N s + 1) → primes,
            movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n
              (fun i => Quotient.mk'' i)
              (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
                ((logSlots j).map (fun i => (e s).symm (.inl i))) : ℝ) : ℂ) *
              movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm
                (fun i => Quotient.mk'' i) primes hprimes p g Dq
                (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
                (frequencyRoot n (trees t false))
                (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
                  (movingPatternRegularSlots (e s) n m small slot)) greg f outside
                childBound pivotBound ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center x) x
        Monotone V → f 0 = 0 →
        (Sfreq.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (∀ s t, ‖term t s‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err)) →
        ‖movingWeightedMatchedCorrelation p (fun q : primes => (q : ℕ)) outside μ ν
          childBound pivotBound V f g Dq Finset.univ ψ X (Real.exp Δ) hi φ G n small
          (movingPatternBulkLeaves n m slot perm)
          (fun s y x z => wgt y * movingTemplateExternalMultiplier primes hprimes n r₀ m active outside greg s
            φ Jleft Jright diagonal y x z) u v r w center‖ ≤
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_good_pattern_rate n k hk Cprior Cfreq gain hCprior hCfreq] with L hrate
  dsimp only at hrate ⊢
  intro r₀ primes hprimes p _ μ ν childBound pivotBound V f g Dq X Δ hi φ G
    active perm greg outside Jleft Jright diagonal u v r w center cb N e
  let m := spectatorBulkCount k L
  let small := movingTemplateSmall n r₀ m
  let slot := movingTemplateBulk n r₀ m
  let logSlots := movingBulkPairedCutoffSlots n (movingPatternBulkLeaves n m slot perm)
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
    frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
  let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
    ∑ x : Fin (N s + 1) → primes,
      movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n (fun i => Quotient.mk'' i)
        (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
                ((logSlots j).map (fun i => (e s).symm (.inl i))) : ℝ) : ℂ) *
              movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm (fun i => Quotient.mk'' i)
          primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
          (frequencyRoot n (trees t false))
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
          ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center x) x
  intro hV hf hcard hterm
  have hsum := hrate Sfreq hcard (fun s t => (‖term t s‖ : ℂ)) (by
    intro s t
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [add_assoc] using hterm s t)
  have hnonneg : 0 ≤ ∑ s : Setoid (Bool × MovingSampleIndex n),
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ‖term t s‖ := by positivity
  simp only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hnonneg] at hsum
  have hactual := movingTemplateLogMatchedCorrelation_pattern_bound primes hprimes outside n r₀
    (spectatorBulkCount k L) perm active p μ ν childBound pivotBound V f hf g Dq ψ X (Real.exp Δ)
    hi φ G greg Jleft Jright diagonal u v r w center cb hV N e
  apply hactual.trans
  rw [Finset.sum_comm]
  exact hsum

end Ostmann

end OAI
