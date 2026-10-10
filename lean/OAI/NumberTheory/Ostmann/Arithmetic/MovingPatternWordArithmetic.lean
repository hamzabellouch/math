import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternWordCellRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSupportedArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternObservableCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalErrorRate

namespace OAI

/-! # The complete original per-pattern arithmetic estimate from the published progression input -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_word_arithmetic_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A lo hi Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (U : ℝ)
        (a b : (TreeLeafIndex (n + 2) × Fin m) → ℝ)
        (h : (TreeLeafIndex (n + 2) × Fin m) → ℕ) (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => wordCellSupport (a j) (b j) (h j)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let obs := movingPatternPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L)
        y ψ X lo hi hlo hhi φ G L U
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
          ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (∀ j, Real.exp ((39 / 10000 : ℝ) * L) ≤ a j) →
      (∀ j, S j ⊆ primes) →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ j, Real.exp (-Cmass * L) ≤
        finiteCellMass (primeLogCellSet 1 0 (a j) (b j) \ global)
          primeLogIndex (fun p => (p : ℝ)⁻¹) (h j)) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (S j \ global)) →
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
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern obs x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
          (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_word_cell_rate ψ n r₀ k A lo hi Bφ Dφ F Cmass gain
      hA hlo hhi hF hCmass hBφ hDφ
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hrate] with L hrate
  dsimp only
  intro Bidx Cidx _ _ N e tierB tierC t small slot perm pattern rep primes hprimes _
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β y X j₀ φ G U a b h global
    μ ν Eprior αall βint Vint Uall hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    ha hS hdel hmass hout hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
  let obs := movingPatternPrimeObservable e t small slot perm pattern primes hprimes
    childBound pivotBound hfreq Fw Ew outside R r p
    (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L)
    y ψ X lo hi hlo hhi φ G L U
  let cost := (2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖) *
    ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
  have hpoint (x) : ‖obs x‖ ≤ cost :=
    movingPatternPrimeObservable_norm e tierB tierC t small slot perm pattern hB htier
      primes hprimes childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L) y j₀
      ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
      hy (fun i => (p i : ℝ)) (fun i => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
  have hminor (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
      ‖movingPatternBulkMean e ν slot obs x‖ ≤
      Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
    exact hrate Bidx Cidx N e tierB tierC t small slot perm pattern primes hprimes x
      childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β y X j₀ φ G U a b h global
      hm hsmall hB htier hsmallLen hR hr hV hp hfreqp (hsmallp x hx) (hsamplesp x hx)
      hgood hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
      ha hS hdel hmass hout ν hν
  have hfinal := movingPattern_signed_arithmetic_on_support e (fun q : primes => (q : ℕ))
    Subtype.val_injective (fun q => hprimes _ q.property) tierB tierC t small
    (movingPatternBulkLeaves (n + 2) m slot perm) pattern rep
    (fun b j _ => hB j) (fun b j _ => hB j) htier
    (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall
    (Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))) hUall
    (movingPatternFinBulkData_size e t small slot perm pattern hsmallLen)
    (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hV)
    (fun q => by
      simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (q : ℕ) from Nat.cast_nonneg _)]
        using hvalues q)
    μ ν hμ0 hν0 hμmass hνmass Eprior αall βint Vint hEprior hαall hβint hVint
    hμbound hμall hνall hμmax hμmin obs cost (by dsimp only [cost]; positivity)
    hpoint hdisjoint hcross hfmod m slot perm rfl
    (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hminor
    (fun _ => Classical.arbitrary primes)
  simpa only [movingInternalArithmeticError, obs, cost, data, m] using hfinal

end Ostmann

end OAI
