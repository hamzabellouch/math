import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternMixedPrimeInitialNormRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeObservable

namespace OAI

/-! # Norm estimate for the original selected-coordinate mean -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- Uniform prime-cell comparison for the actual arithmetic absolute mean.
The sharp Fourier window factor is retained in the main term. The published
progression input controls the cell, collision and deletion errors. -/
theorem PublishedProgressionInput.movingPattern_selected_mixed_prime_norm_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ F Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (base : Fin (N + 1) → primes)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (y X A₀ : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ),
      let data := movingPatternFinBulkData e n m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let freq := frozenBulkFrequencyFactor (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) outside
        Fw Ew data childBound R r P Qfreq y
      let spec := fun i => frozenBulkSpectatorHaar (fun i => (base i : ℕ)) n m t
        (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
        (twist i) perm (normalizedResidueTransform (sets i))
      let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
        ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (base i : ℕ) ∈ deleted j) →
      (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
      0 ≤ A₀ →
      (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
        (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
          ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
            (w j).val.val (z j)‖ ≤ A₀) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ∀ initial : (TreeLeafIndex n × Fin m) → Finset ℕ,
      (∀ j, initial j ⊆ S j) → (∀ j, S j \ deleted j ⊆ initial j) →
      ∀ ν : Bidx → primes → ℝ,
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      ‖movingPatternBulkMean e ν slot
        (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
          childBound pivotBound hfreq Fw Ew outside R r p
          (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
          y ψ X lo hi hlo hhi φ G XL U) base‖ ≤
        ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  filter_upwards [P.movingPattern_initial_mixed_prime_norm_rate ψ n r₀ k A Wwin Bφ Dφ F Cmass
    hA hWwin hF hCmass hBφ hDφ] with L hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern primes hprimes base
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets Qfreq y X A₀ j₀ φ G XL U u v deleted
    hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hy hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout hA₀ hlocal c₀
    initial hsub hretain ν hν
  rw [movingPatternBulkMean_primeObservable]
  · exact hrate lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t small slot perm pattern
      (fun i => (base i : ℕ)) primes hprimes (fun i _ => hprimes _ (base i).property)
      childBound pivotBound hfreq Fw Ew outside R r p hc twist sets Qfreq y X A₀ j₀ φ G XL U u v deleted
      hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hy hpupper hMQ hφ hlip hφout
      hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout hA₀ hlocal c₀
      initial hsub hretain
  · exact hν

end Ostmann

end OAI
