import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateEnergyPatterns
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticDiagonalPatternNormRate

namespace OAI

/-! # Applying the numerical pattern budget to the original masked energy -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateDiagonalEnergy_pattern_rate
    (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (Bwindow Cfreq Cprior ε : ℝ) (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior)
    (hε : 0 < ε) (hdepth : 8 * Cprior ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ d : ℕ, d ≠ 0 → (d : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (d.divisors.card : ℝ) ≤ D) ∧
        ∀ (r₀ : ℕ)
          (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
          (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
          (μ : ℕ → primes → ℝ) (ν : MovingRegularSlot n r₀ m → primes → ℝ)
          (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
          (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
          (X Δ hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
          (active : MovingRegularSlot n r₀ m → Bool)
          (greg : ∀ q : ℕ, ZMod q → ℂ) (outside : List ℕ)
          (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
          (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
          (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ MovingRegularSlot n r₀ m ⊕ Quotient s),
        let small := movingTemplateSmall n r₀ m
        let slot := movingTemplateBulk n r₀ m
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let Sfreq := (transferFrequencyRange (V n)).erase 0
        let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
          frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
        let K := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            Bwindow ^ (2 ^ n - 1)) ^ 2 *
          ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m)
        let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
        let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
          ∑ x : Fin (N s + 1) → primes,
            movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n
              (fun i => Quotient.mk'' i)
              (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot
                (fun i => Quotient.mk'' i) primes hprimes p g Dq
                (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
                (frequencyRoot n (trees t false))
                (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
                  (movingPatternRegularSlots (e s) n m small slot)) greg f outside
                childBound pivotBound ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center) x
        Monotone V → f 0 = 0 →
        (Sfreq.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (V n : ℝ) ≤ Real.exp (Cfreq * m) →
        (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        (∀ s t, ‖term t s‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (err + K * (frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
            ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod))) →
        ‖movingWeightedDiagonalEnergy p (fun q : primes => (q : ℕ)) outside μ ν
          childBound pivotBound V f g Dq Finset.univ ψ X (Real.exp Δ) hi φ G n small
          (bulkSlotLeaves n m slot)
          (fun s => movingTemplateExternalMultiplier primes hprimes n r₀ m active outside greg s φ
            Jleft Jright diagonal) u v r w center‖ ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_diagonal_pattern_norm_rate ψ n k hk hn
    Bwindow Cfreq Cprior ε hCfreq hCprior hε hdepth] with L hrate
  dsimp only at hrate ⊢
  obtain ⟨D, hD, hdiv, hrate⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro r₀ primes hprimes p _ μ ν childBound pivotBound V f g Dq X Δ hi φ G
    active greg outside Jleft Jright diagonal u v r w center N e
  let m := spectatorBulkCount k L
  let small := movingTemplateSmall n r₀ m
  let slot := movingTemplateBulk n r₀ m
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
    frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
  let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
    ∑ x : Fin (N s + 1) → primes,
      movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n (fun i => Quotient.mk'' i)
        (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot (fun i => Quotient.mk'' i)
          primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
          (frequencyRoot n (trees t false))
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
          ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center) x
  intro hV hf hcard hVn hV0 hterm
  have hS : ∀ s ∈ Sfreq, s ≠ 0 ∧ s.natAbs ≤ V n := by
    intro s hs
    exact ⟨(Finset.mem_erase.mp hs).1,
      (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2⟩
  have hsum := hrate Sfreq (V n) (V 0) Δ
    (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hcard hS hVn hV0 (by positivity) le_rfl
    (fun s t => (‖term t s‖ : ℂ)) (by
      intro s t
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      exact hterm s t)
  have hnonneg : 0 ≤ ∑ s : Setoid (Bool × MovingSampleIndex n),
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ‖term t s‖ := by positivity
  simp only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hnonneg] at hsum
  have hactual := movingTemplateDiagonalEnergy_pattern_bound primes hprimes outside n r₀
    (spectatorBulkCount k L) active p μ ν childBound pivotBound V f hf g Dq ψ X (Real.exp Δ)
    hi φ G greg Jleft Jright diagonal u v r w center hV N e
  apply hactual.trans
  rw [Finset.sum_comm]
  exact hsum

end Ostmann

end OAI
