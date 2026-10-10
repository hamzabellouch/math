import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalEnergyPatterns
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticTwoPrimePatternNormRate

namespace OAI

/-! # The sharp pattern budget applied to the actual coefficient energy -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

/-- This is the actual external-prior coefficient energy. The local premise
is precisely the original prime-pattern bound, with its retained split
probabilities; it is supplied by the prime arithmetic comparison. -/
theorem movingFrequencyCoefficient_original_pattern_rate
    (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (Bwindow Cfreq Cprior ε : ℝ) (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior)
    (hε : 0 < ε) (hdepth : 8 * (Cprior + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ d : ℕ, d ≠ 0 → (d : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (d.divisors.card : ℝ) ≤ D) ∧
        ∀ (σ I B : Type) [Fintype σ] [Fintype B]
          (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
          (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
          (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
          (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (P : Finset I)
          (X Δ hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
          (small bulk : TreeLeafTuple (List B) n) (u v r w : ℝ)
          (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
          (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let Sfreq := (transferFrequencyRange (V n)).erase 0
        let K := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            Bwindow ^ (2 ^ n - 1)) ^ 2 *
          ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m)
        let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
        let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
          ∑ x : Fin (N s + 1) → σ,
            movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
              (movingOriginalPatternPrimeObservable (e s) (fun i => Quotient.mk'' i) q value
                outside childBound pivotBound F g Dq P ψ X (Real.exp Δ) hi φ G
                (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t))
                small bulk u v r w) x
        Monotone V → (∀ d (T : MovingSlotData σ d), F T 0 = 0) →
        (Sfreq.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (V n : ℝ) ≤ Real.exp (Cfreq * m) →
        (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        (∀ s t, ‖term t s‖ ≤
          ((4 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (err + K * (frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
            ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod))) →
        ‖∑ a : transferFrequencyRange (V n), ∑ z : B → σ, ((∏ b, ν b (z b) : ℝ) : ℂ) *
          complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun x =>
            (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
              (movingOriginalLeaf value q F g Dq P ψ X (Real.exp Δ) hi) φ G n a.val
              (treeLeafMap (List.map z) n small) (treeLeafMap (List.map z) n bulk)
              ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ)))‖ ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_two_prime_original_pattern_norm_rate ψ n k hk hn
    Bwindow Cfreq Cprior ε hCfreq hCprior hε hdepth] with L hrate
  dsimp only at hrate ⊢
  obtain ⟨D, hD, hdiv, hrate⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro σ I B _ _ q _ value outside μ ν childBound pivotBound V F g Dq P X Δ hi φ G
    small bulk u v r w N e
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
    ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (movingOriginalPatternPrimeObservable (e s) (fun i => Quotient.mk'' i) q value
          outside childBound pivotBound F g Dq P ψ X (Real.exp Δ) hi φ G
          (fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t))
          small bulk u v r w) x
  intro hV hF hcard hVn hV0 hterm
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
  have hactual := movingFrequencyCoefficient_original_pattern_bound q value outside μ ν
    childBound pivotBound V F g Dq P ψ X (Real.exp Δ) hi φ G n small bulk u v r w hV hF N e
  apply hactual.trans
  rw [Finset.sum_comm]
  exact hsum

end Ostmann

end OAI
