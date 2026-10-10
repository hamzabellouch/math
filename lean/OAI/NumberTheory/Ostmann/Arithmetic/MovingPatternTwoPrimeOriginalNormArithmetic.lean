import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTwoPrimeSelectedNormRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePatternSupportedArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTwoPrimeObservableCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalErrorRate

namespace OAI

/-! # The norm estimate with the original internal and external priors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_two_prime_norm_arithmetic_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ F Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (xg y X A₀ : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e n m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 4 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let obs := movingPatternTwoPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        xg y ψ X lo hi hlo hhi φ G XL U
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      amp ≤ Real.exp (F * m) → 0 ≤ xg → 0 ≤ y →
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
      (∀ x, productPrior law x ≠ 0 →
        ∀ j, ((deleted x j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → (x i : ℕ) ∈ deleted x j) →
      (∀ q ∈ outside, q.Prime) →
      (∀ x, productPrior law x ≠ 0 → ∀ j q, q ∈ outside → q ∈ deleted x j) →
      0 ≤ A₀ →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        let freq := frozenBulkFrequencyPrime (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot)
          outside Fw Ew data childBound R r P Qfreq xg y
        let spec := fun i => frozenBulkSpectatorPrime (fun i => (x i : ℕ)) n m t
          (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
          (twist i) perm (normalizedResidueTransform (sets i))
        let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
          ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
        ∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
          (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
            ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
              (w j).val.val (z j)‖ ≤ A₀) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      (∀ j, initial j ⊆ S j) →
      (∀ x, productPrior law x ≠ 0 → ∀ j, S j \ deleted x j ⊆ initial j) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (initial j)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern obs x *
        movingPatternPrimeHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          n t small (movingPatternBulkLeaves n m slot perm) pattern x‖ ≤
      ((4 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  filter_upwards [P.movingPattern_selected_two_prime_norm_rate ψ n r₀ k
    A Wwin Bφ Dφ F Cmass hA hWwin hF hCmass hBφ hDφ] with L hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t small slot perm pattern rep primes hprimes _
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets Qfreq xg y X A₀ j₀ φ G XL U u v deleted initial
    μ ν Eprior αall βint Vint Uall hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hxg hy hpupper
    hMQ hφ hlip hφout hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout
    hA₀ hlocal c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let obs := movingPatternTwoPrimeObservable e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq Fw Ew outside R r p
    (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
    xg y ψ X lo hi hlo hhi φ G XL U
  let cost := (4 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖) *
    ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hpoint (x) : ‖obs x‖ ≤ cost :=
    movingPatternTwoPrimeObservable_norm e tierB tierC t small slot perm pattern hB htier
      primes hprimes childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P Qfreq xg y j₀
      ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout XL U
      hxg hy (fun i => (p i : ℝ)) (fun i => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
  have hminor (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
      ‖movingPatternBulkMean e ν slot obs x‖ ≤
      (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
    exact hrate lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t small slot perm pattern primes hprimes x
      childBound pivotBound hfreq Fw Ew outside R r p hc twist sets Qfreq xg y X A₀ j₀ φ G XL U u v (deleted x)
      hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hxg hy hpupper hMQ hφ hlip hφout
      hcard hu hulow huv hshort hsep hMcell hS (hdel x hx) hmass (hdelbase x hx) hout (hdelout x hx)
      hA₀ (hlocal x hx) c₀ initial hsub (hretain x hx) ν hν
  have hfinal := movingPrimePattern_signed_arithmetic_on_support e (fun q : primes => (q : ℕ))
    Subtype.val_injective (fun q => hprimes _ q.property) tierB tierC t small
    (movingPatternBulkLeaves n m slot perm) pattern rep
    (fun b j _ => hB j) (fun b j _ => hB j) htier
    (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall
    (Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))) hUall
    (movingPatternFinBulkData_size e t small slot perm pattern hsmallLen)
    (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hV)
    (fun q => by
      simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (q : ℕ) from Nat.cast_nonneg _)]
        using hvalues q)
    μ ν hμ0 hν0 hμmass hνmass Eprior αall βint Vint hEprior hαall hβint hVint
    hμbound hμall hνall hμmax hμmin obs cost (by dsimp only [cost]; positivity)
    hpoint hdisjoint hcross hfmod m slot perm rfl
    ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hminor
    (fun _ => Classical.arbitrary primes)
  simpa only [movingInternalArithmeticError, obs, cost, data, m] using hfinal

end Ostmann

end OAI
