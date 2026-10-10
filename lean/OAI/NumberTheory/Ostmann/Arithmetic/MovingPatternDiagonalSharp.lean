import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternDiagonalArithmetic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalNumericalRate

namespace OAI

/-! # The sharp original-prior diagonal estimate after absorbing the comparison errors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_diagonal_sharp
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass Cprior : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) (hCprior : 1 ≤ Cprior) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
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
        (_hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG center : ℝ),
      let reg := (movingPatternRegularSlots e n m small slot).get
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      MovingLeafLengthLE n small r₀ →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
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
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ j, active j = false → reg j ∉ Set.range (movingPatternBulkEmbedding e slot)) →
      Function.Injective p →
      (∀ q ∈ outside, ∃ i, p i = q) →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      ∀ (tier : primes → ℕ) (lower cutoff : ℕ),
      Nfreq ≤ lower → Nfreq < cutoff → cutoff ≤ lower →
      (∀ j, j < n → ∀ q, μ j q ≠ 0 → tier q = j) →
      (∀ j q, ν j q ≠ 0 → tier q = tierB j) →
      (∀ j q, μ j q ≠ 0 → lower < (q : ℕ)) →
      (∀ j q, ν j q ≠ 0 → lower < (q : ℕ)) →
      (∀ q : primes, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ lower) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      Eprior ≤ Real.exp (Cprior * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq reg active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx *
        (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
      ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
        Bφ ^ (2 ^ n - 1)) ^ 2) * A₀ * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
        Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  filter_upwards [P.movingPattern_original_diagonal_arithmetic_rate ψ n r₀ k A Wwin Bφ Dφ Cmass
    hA hWwin hCmass hBφ hDφ,
    movingPattern_diagonal_pointwise_rate ψ n r₀ k A Wwin Bφ Dφ Cprior Cmass
      hA hWwin hBφ hDφ hCprior (by linarith)] with L hmain hrate
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D
    small slot pattern rep primes hprimes _ childBound pivotBound hfreq f outside _ p _ hc _
    Dq sets X j₀ φ G u v deleted initial μ ν active sreg setsReg Jleft Jright diagonal
    Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hcenter
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hfixed
    hinjp houtp hNupper hcenterlow hrGlow tier lower cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hprange hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg hEup hUlog hαup hβup hVeq
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern
  let amp := 2 * (‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data false)‖ *
    ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data true)‖)
  let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
    (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
      ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
  let K := (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
    Bφ ^ (2 ^ n - 1)) ^ 2) * A₀ * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)
  have hh := hmain lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq Vleaf D
    small slot pattern rep primes hprimes childBound pivotBound hfreq f outside p hc Dq sets X j₀ φ G
    u v deleted initial μ ν active sreg setsReg Jleft Jright diagonal Eprior αall βint Vint Uall
    uG vG rG sG center huG hrG huvG hrsG hvG hsG hcenter hsmall hB htier hsmallLen ht hS hN hleaf
    hD hdiv hm hp hV hsets hsetsp hpupper hMQ hφ hlip hφout hcard hu hulow huv hshort hsep hMcell
    hSS hdel hmass hdelbase hout hdelout c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall
    hβint hVint hUall hμbound hμall hνall hμmax hμmin hvalues hfixed hinjp houtp hNupper hcenterlow
    hrGlow tier lower cutoff hNlo hNcut hcutlo hμtier hνtier hμlo hνlo hupper hprange
    hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  have hone (b : Bool) : ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1) (data b)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one (fun {_} _ => f)
      (fun s _ => (hleaf s).trans (by split_ifs <;> norm_num)) (data b)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hamp : amp ≤ 4 := by
    have h := mul_le_mul (hone false) (hone true) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp only [amp]
    linarith
  have hK : 0 ≤ K := by
    have hf := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hs : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact pairFrequencySupportBound_nonneg D b
    dsimp only [K, A₀]
    positivity
  apply hrate p (Fintype.card Cidx) Eprior Uall αall βint amp lo hi rG K _ diagonal
    (movingPattern_class_card_le n pattern rep) hEprior hEup hUall hUlog hαall hαup hβint hβup
    hamp0 hamp hhi hwindow hpupper hrGlow hK
  simpa only [hVeq, add_assoc] using hh

end Ostmann

end OAI
