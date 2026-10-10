import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTwoPrimeOriginalNormArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeNormalizedNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFrequencyModulus
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSupportedArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternObservableCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalErrorRate

namespace OAI

/-! # The norm estimate with the original internal and external priors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_same_assignment_two_prime_arithmetic_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (xg y X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 4 * (‖movingDataWeight (Fw false) ((fun _ _ _ _ _ => 1) false) (data false)‖ *
        ‖movingDataWeight (Fw true) ((fun _ _ _ _ _ => 1) true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let obs := movingPatternTwoPrimeObservable e t small slot (Equiv.refl _) pattern primes hprimes
        childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside ((frequencyModelBase Sfreq n ft) : ℤ) ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        xg y ψ X lo hi hlo hhi φ G XL U
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) → (∀ i b, movingGiantFrequencyUnits (p i) n (t b)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → IsCoprime ((x i : ℕ) : ℤ) ((frequencyModelBase Sfreq n ft) : ℤ)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i b j,
        j ∈ flattenMovingSlots n (small b) → ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i c,
        ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      0 ≤ xg → 0 ≤ y →
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
          n t small (movingPatternBulkLeaves n m slot (Equiv.refl _)) pattern x‖ ≤
      ((4 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError n (Fintype.card Cidx)
          (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        ((((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  filter_upwards [P.movingPattern_original_two_prime_norm_arithmetic_rate ψ n r₀ k
    A Wwin Bφ Dφ 2 Cmass hA hWwin (by norm_num) hCmass hBφ hDφ] with L hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound hfreq Fw outside _ p _ hc _ twist sets
    Qfreq xg y X j₀ φ G XL U u v deleted initial μ ν Eprior αall βint Vint Uall
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
    hsmallp hsamplesp hV hsets hsetsp hxg hy hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let R := frequencyModelBase Sfreq n ft
  have hR (b : Bool) : (movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern b).frequencyProduct ∣ (R : ℤ) := by
    simpa only [ht, R] using movingPattern_frequencyProduct_dvd e Sfreq ft small slot (Equiv.refl _) pattern b
  have hroots (b : Bool) (j : Fin (2 ^ n - 1)) :
      (singleTreeNodeFrequencies Sfreq n (frequencyPairProjection Sfreq n b ft) j.val).root.natAbs ∣ R :=
    frequencyModelBase_roots Sfreq n ft b j
  let data := movingPatternFinBulkData e n m t small slot (Equiv.refl _) pattern
  have hone (b : Bool) : ‖movingDataWeight (Fw b) (fun _ _ _ _ => 1) (data b)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (Fw b) (fun s regular =>
      (hleaf b s regular).trans (by split_ifs <;> norm_num)) (data b)
  have hamp : 4 * (‖movingDataWeight (Fw false) (fun _ _ _ _ => 1) (data false)‖ *
      ‖movingDataWeight (Fw true) (fun _ _ _ _ => 1) (data true)‖) ≤ Real.exp ((2 : ℝ) * m) := by
    have hpair := mul_le_mul (hone false) (hone true) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have he : (2 : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
    calc
      _ ≤ 4 := by linarith
      _ ≤ (Real.exp (m : ℝ)) ^ 2 := by nlinarith [Real.exp_pos (m : ℝ)]
      _ = _ := by simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (m : ℝ) 2).symm
  let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
    (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
      ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
  have hA₀ : 0 ≤ A₀ := by
    have hleaf0 := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hprod : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact pairFrequencySupportBound_nonneg D f
    exact mul_nonneg (by positivity) (mul_nonneg hleaf0 hprod)
  have hlocal (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0)
      (z : (TreeLeafIndex n × Fin m) → ℝ) (hz : ∀ j, 0 ≤ z j) :=
    movingPattern_normalized_same_assignment_prime_norm e tierB tierC Sfreq ft R Nfreq Vleaf
      hS hN hroots small slot pattern hsmall hB htier (fun i => (x i : ℕ)) (hbase x hx)
      Fw hleaf D hD hdiv hm p hc hp
      (by simpa only [ht] using hfreqp) (hsmallp x hx) (hsamplesp x hx)
      sets hsets hsetsp twist outside childBound P Qfreq (bulkProgressionCutoff L) xg y hxg hy z hz
  have h := hrate lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t small slot (Equiv.refl _) pattern rep
    primes hprimes childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside (R : ℤ)
    (R ^ (n - 1 + 2)) p hc twist sets Qfreq xg y X A₀ j₀ φ G XL U u v deleted initial μ ν
    Eprior αall βint Vint Uall hsmall hB htier hsmallLen hR (frequencyModelModulus_precision R n)
    hV hsets hsetsp hamp hxg hy hpupper hMQ hφ hlip hφout hcard hu hulow huv hshort hsep hMcell
    hSS hdel hmass hdelbase hout hdelout hA₀
    (by
      intro x hx
      dsimp only
      intro z hz
      have hz' := hlocal x hx z hz
      simpa only [A₀, m, ht, finite_univ_canonical, Fintype.card_eq_nat_card, Nat.card_fin] using hz')
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
  exact h

end Ostmann

end OAI
