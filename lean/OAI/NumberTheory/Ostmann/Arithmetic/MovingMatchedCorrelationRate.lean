import OAI.NumberTheory.Ostmann.Arithmetic.MovingMatchedCorrelationPatterns
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticGoodPatternRate

namespace OAI

/-! # Full original matched correlation from the signed pattern budget -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalMatchedCorrelation_pattern_rate
    (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k)
    (Cfreq Cprior gain : ℝ) (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
        ∀ (B : Type) [Fintype B]
          (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
          (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
          (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
          (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
          (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
          (X Δ hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
          (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
          (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
          (greg : ∀ q : ℕ, ZMod q → ℂ) (outside : List ℕ)
          (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
          (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
          (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
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
              (movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm
                (fun i => Quotient.mk'' i) primes hprimes p g Dq
                (movingPatternRegularSlots (e s) n m small slot).get (fun _ => true)
                (frequencyRoot n (trees t false))
                (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
                  (movingPatternRegularSlots (e s) n m small slot)) greg f outside
                childBound pivotBound ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center) x
        Monotone V → f 0 = 0 →
        (Sfreq.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (∀ s t, ‖term t s‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err)) →
        ‖movingOriginalMatchedCorrelation p (fun q : primes => (q : ℕ)) outside μ ν
          childBound pivotBound V f g Dq Finset.univ ψ X (Real.exp Δ) hi φ G n small
          (movingPatternBulkLeaves n m slot perm) greg Jleft Jright diagonal u v r w center‖ ≤
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_good_pattern_rate n k hk Cprior Cfreq gain hCprior hCfreq] with L hrate
  dsimp only at hrate ⊢
  intro B _ primes hprimes p _ μ ν childBound pivotBound V f g Dq X Δ hi φ G
    small slot perm greg outside Jleft Jright diagonal u v r w center N e
  let m := spectatorBulkCount k L
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
    frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
  let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
    ∑ x : Fin (N s + 1) → primes,
      movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n (fun i => Quotient.mk'' i)
        (movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm (fun i => Quotient.mk'' i)
          primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get (fun _ => true)
          (frequencyRoot n (trees t false))
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
          ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center) x
  intro hV hf hcard hterm
  have hsum := hrate Sfreq hcard (fun s t => (‖term t s‖ : ℂ)) (by
    intro s t
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [add_assoc] using hterm s t)
  have hnonneg : 0 ≤ ∑ s : Setoid (Bool × MovingSampleIndex n),
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ‖term t s‖ := by positivity
  simp only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hnonneg] at hsum
  have hactual := movingOriginalMatchedCorrelation_pattern_bound primes hprimes outside n
    (spectatorBulkCount k L) p μ ν childBound pivotBound V f hf g Dq ψ X (Real.exp Δ)
    hi φ G small slot perm greg Jleft Jright diagonal u v r w center hV N e
  apply hactual.trans
  rw [Finset.sum_comm]
  exact hsum

end Ostmann

end OAI
