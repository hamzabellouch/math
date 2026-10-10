import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternOriginalPrimeArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternInternalError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeNormBudget

namespace OAI

/-! # The original prime pattern bound with all numerical errors discharged -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_prime_sharp_rate
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
        (small : TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (Qfreq : ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG : ℝ),
      let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
      let data := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
      let coeff := movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1)
      let Pi := fun x => movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x
      let Mgiant := fun x => ∏ z, movingArithmeticModuli
        ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p (Pi x) Finset.univ z
      let Reg := fun x => MovingSlotReversal.naturalProduct (fun i => (x i : ℕ))
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let obs := fun xg y => movingPatternTwoPrimeObservable e t (fun _ => small) slot (Equiv.refl _) pattern primes hprimes
        childBound pivotBound hfreq Fw (fun _ _ _ _ _ => 1) outside ((frequencyModelBase Sfreq n ft) : ℤ) ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (fun i => normalizedResidueTransform (sets i)) (fun i _ => Dq i) P Qfreq
        xg y ψ X lo hi hlo hhi φ G (Real.exp xg) (Real.exp y)
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots n ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b : Bool, MovingLeafLengthLE n ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) → (∀ i b, movingGiantFrequencyUnits (p i) n (t b)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → IsCoprime ((x i : ℕ) : ℤ) ((frequencyModelBase Sfreq n ft) : ℤ)) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i (b : Bool) j,
        j ∈ flattenMovingSlots n ((fun _ => small) b) → ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 → ∀ i c,
        ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
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
      1 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ xg ∈ Set.Ioc uG vG, ∀ y ∈ Set.Ioc rG sG, ∀ x, productPrior law x ≠ 0 → obs xg y x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      (∀ i, ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)).Coprime (p i)) →
      (∀ i, Nfreq < p i) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ Nfreq) →
      2 ≤ Qfreq →
      Real.log (4 * (Qfreq : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ uG →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Eprior ≤ Real.exp (Cmass * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      (∀ x, coeff x ≠ 0 →
        (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) ∧
        (∀ i, Nfreq < (x i : ℕ)) ∧
        (∀ i, IsCoprime ((x i : ℕ) : ℤ) (frequencyModelBase Sfreq n ft : ℤ)) ∧
        (∀ i, ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)).Coprime (x i : ℕ)) ∧
        (∀ i j, ((x j : ℕ) : ZMod (p i)) ≠ 0) ∧
        Mgiant x ≤ Qfreq ∧
        pageAtModulus (Mgiant x) (selectedPageZero P Qfreq) =
          pageAtModulus ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) (selectedPageZero P Qfreq) ∧
        Real.log (Mgiant x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) ∧
        Real.log (Reg x : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternPrimeObservable e pattern p (fun q : primes => (q : ℕ))
          outside childBound pivotBound (fun {_} _ => f)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X lo hi φ G t
          small (bulkSlotLeaves n m slot) uG vG rG sG) x‖ ≤
        ((4 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) +
            ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
              Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) *
                2 ^ Fintype.card (TreeLeafIndex n × Fin m)) := by
  obtain ⟨Cbudget, _, hbudget⟩ := movingPattern_giant_variation_budget ψ n r₀ k
    A Wwin Bφ Dφ hA hWwin
  filter_upwards [P.movingPattern_original_prime_arithmetic_rate ψ n r₀ k Cbudget 2
    A Wwin Bφ Dφ Cmass hA hWwin hCmass hBφ hDφ,
    movingPattern_internal_arithmetic_error_rate ψ n r₀ k A Wwin Bφ Dφ Cmass
      hA hWwin (by linarith), movingPattern_original_prime_norm_budget n Cmass hCmass,
    eventually_ge_atTop (1 : ℝ)] with L hraw herr hnorm hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound hfreq f outside _ p _ hc _ Dq sets
    Qfreq X j₀ φ G u v deleted initial μ ν Eprior αall βint Vint Uall uG vG rG sG
    huG hrG huvG hrsG hvG hsG
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hfreqp hbase
    hsmallp hsamplesp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
    houtcover hinjp hrp hspecN hfreqN hQ hQlog huBig hrBig hNfreq hEup hαup hβup hVeq hUlog hUup hdata
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
    (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
      ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
  let amp := 4 * (‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data false)‖ *
    ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data true)‖)
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
      (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  let main := ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
    Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)
  have hg := hbudget L hL p Nfreq lo hi (Nat.cast_nonneg _) hNfreq hhi hwindow hpupper
  have hb := hraw lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq
    Vleaf D small slot pattern rep primes hprimes childBound pivotBound hfreq f outside p hc
    Dq sets Qfreq X j₀ φ G u v deleted initial μ ν Eprior αall βint Vint Uall uG vG rG sG
    huG hrG huvG hrsG hvG hsG hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp
    hfreqp hbase hsmallp hsamplesp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass (by linarith) hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
    houtcover hinjp hrp hspecN hfreqN hQ hQlog huBig hrBig hg hdata
  have hf (s : ℤ) : ‖f s‖ ≤ 1 := (hleaf false s []).trans (by split_ifs <;> norm_num)
  have hone (b : Bool) : ‖movingDataWeight (fun {_} _ => f)
      (fun _ _ _ _ => 1) (data b)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (fun {_} _ => f) (fun s _ => hf s) (data b)
  have hamp : amp ≤ 4 := by
    have hp := mul_le_mul (hone false) (hone true) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp only [amp]
    nlinarith
  have hcost0 : 0 ≤ cost := by dsimp only [cost, amp]; positivity
  have herror0 := movingInternalArithmeticError_nonneg n (Fintype.card Cidx)
    (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint
    (Real.one_le_exp (mul_nonneg hA (Nat.cast_nonneg m))) hUall hαall hβint hVint.le
  have hcnum := movingPattern_class_card_le n pattern rep
  have he := herr p (Fintype.card Cidx) Uall αall βint amp lo hi hcnum hUall hUlog
    hαall hαup hβint hβup (by dsimp only [amp]; positivity) hamp hhi hwindow hpupper
  rw [← hVeq] at he
  have hA₀ : 0 ≤ A₀ := by
    have hleaf0 := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hprod : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro z hz
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hz
      exact pairFrequencySupportBound_nonneg D f
    exact mul_nonneg (by positivity) (mul_nonneg hleaf0 hprod)
  have hmain : 0 ≤ main := by dsimp only [main]; positivity
  exact hnorm (Fintype.card Cidx) Eprior Uall uG rG
    (cost * movingInternalArithmeticError n (Fintype.card Cidx)
      (2 ^ n * (r₀ + m + 4 * n + 4)) (Real.exp (A * m)) Uall αall βint Vint)
    main (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) _ hcnum hEprior hEup
    (by linarith) hUup huG hrG (mul_nonneg hcost0 herror0) hmain (by positivity)
    he le_rfl (by simpa only [cost, amp, data, main, A₀, add_assoc] using hb)

end Ostmann

end OAI
