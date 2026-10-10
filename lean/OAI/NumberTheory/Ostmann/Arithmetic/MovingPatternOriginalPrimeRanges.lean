import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternOriginalPrimeSharp
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantConditions
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPriorArithmetic

namespace OAI

/-! # The original prime bound from actual ranges and conductor deletion -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_original_prime_range_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
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
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (Fin (N + 1) → primes) →
          (TreeLeafIndex n × Fin m) → Finset ℕ)
        (initial : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ) (uG vG rG sG : ℝ),
      let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots n ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b : Bool, MovingLeafLengthLE n ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
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
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ uG →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      Eprior ≤ Real.exp (Cmass * L) →
      αall ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      βint ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      Vint = Real.exp ((1 / 100 : ℝ) * L) →
      Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) →
      (∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j) →
      (∀ j a, ν j a ≠ 0 → tier a = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (∀ j a, μ j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ j a, ν j a ≠ 0 → primeLo < (a : ℕ)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, μ j a ≠ 0 → (a : ℕ) ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
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
  filter_upwards [P.movingPattern_original_prime_sharp_rate ψ n r₀ k
    A Wwin Bφ Dφ Cmass hA hWwin hCmass hBφ hDφ,
    movingPattern_giant_conditions P n r₀ k A hA, eventually_ge_atTop (200 : ℝ)]
    with L hsharp hgiant hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ Cell _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound f outside _ p _ hc _ Dq sets
    primeLo cutoff tier X j₀ φ G u v deleted initial μ ν Eprior αall βint Vint Uall uG vG rG sG
    huG hrG huvG hrsG hvG hsG
    hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues
    houtcover hinjp huBig hrBig hNfreq hEup hαup hβup hVeq hUlog hUup hμtier hνtier hNlo hNcut hcutlo hμlo hνlo hupper hpband hdeleteμ hdeletep
  have hmem (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s ∈ Sfreq := by
    rw [ht] at hs
    exact allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n b ft) s hs
  have hfreq (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s ≠ 0 :=
    hS s (hmem b s hs)
  have hfreqN (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s.natAbs ≤ Nfreq :=
    hN s (hmem b s hs)
  have hV (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) :
      |(s : ℝ)| ≤ Real.exp (A * spectatorBulkCount k L) := by
    have hn : (s.natAbs : ℝ) ≤ Nfreq := by exact_mod_cast hfreqN b s hs
    have hr : |(s : ℝ)| ≤ Nfreq := by simpa only [Nat.cast_natAbs, Int.cast_abs] using hn
    exact hr.trans hNfreq
  have htierC : tierC = fun c => movingSampleTier (rep c).val.2 := by
    funext c
    have h := htier (rep c).val
    simpa only [(rep c).property] using h
  have hdata := hgiant primes Bidx Cidx N e (fun q : primes => (q : ℕ)) tier tierB μ ν
    pattern rep Sfreq Nfreq ft small slot p primeLo cutoff Eprior
    Subtype.val_injective (fun a => hprimes _ a.property) hμ0 hν0 hμbound hμtier hνtier hB
    (fun s hs => ⟨hS s hs, hN s hs⟩) hNfreq hNlo hNcut hcutlo hμlo hνlo hupper
    (fun i => ⟨Fact.out, (hpband i).1, (hpband i).2, hpupper i⟩)
    (hsmallLen false) hdeleteμ hdeletep
  have hdata' : ∀ x : Fin (N + 1) → primes,
      movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern (fun _ => 1) x ≠ 0 →
      (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) ∧
      (∀ i, Nfreq < (x i : ℕ)) ∧
      (∀ i, IsCoprime ((x i : ℕ) : ℤ) (frequencyModelBase Sfreq n ft : ℤ)) ∧
      (∀ i, ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)).Coprime (x i : ℕ)) ∧
      (∀ i j, ((x j : ℕ) : ZMod (p i)) ≠ 0) ∧
      (∏ z, movingArithmeticModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x) Finset.univ z) ≤ giantProgressionCutoff L ∧
      pageAtModulus (∏ z, movingArithmeticModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x) Finset.univ z)
        (selectedPageZero P (giantProgressionCutoff L)) =
        pageAtModulus ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2))
          (selectedPageZero P (giantProgressionCutoff L)) ∧
      Real.log ((∏ z, movingArithmeticModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p
        (movingPatternInternalPrimes e (fun q : primes => (q : ℕ)) x) Finset.univ z : ℕ) : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) ∧
      Real.log (MovingSlotReversal.naturalProduct (fun i => (x i : ℕ))
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n _ (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
    simpa only [htierC] using hdata
  have hsupport (x : Fin (N + 1) → primes)
      (hx : productPrior (fun i => Sum.elim ν
        (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :=
    movingPattern_prior_arithmetic_support e μ ν (fun q : primes => (q : ℕ))
      Subtype.val_injective (fun q => hprimes _ q.property) pattern rep tier tierB tierC
      hμtier hνtier hB htier Sfreq Nfreq primeLo ft (fun s hs => ⟨hS s hs, hN s hs⟩)
      hNlo hμlo hνlo p (fun i => Fact.out) (fun i => (hpband i).2) t (fun _ => small)
      slot (Equiv.refl _) hfreq hfreqN x hx
  have hspecN (i) : Nfreq < p i := hNcut.trans_le (hpband i).1
  have hfreqp (i) (b : Bool) : movingGiantFrequencyUnits (p i) n (t b) :=
    movingGiantFrequencyUnits_of_bounds (t b)
      (fun s hs => ⟨hfreq b s hs, (hfreqN b s hs).trans_lt (hspecN i)⟩)
  have hrp (i) : ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)).Coprime (p i) :=
    ((prime_coprime_frequencyModelBase Sfreq Nfreq (p i) n Fact.out (hspecN i)
      (fun s hs => ⟨hS s hs, hN s hs⟩) ft).pow_right _).symm
  have hQ := giantProgressionCutoff_bounds L hL
  exact hsharp lo hi hlo hhi hwindow Bidx Cidx Cell N e tierB tierC t Sfreq ft Nfreq
    Vleaf D small slot pattern rep primes hprimes childBound pivotBound hfreq f outside p hc
    Dq sets (giantProgressionCutoff L) X j₀ φ G u v deleted initial μ ν Eprior αall βint Vint Uall uG vG rG sG
    huG hrG huvG hrsG hvG hsG hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp
    hfreqp (fun x hx i _ => (hsupport x hx).1 i)
    (fun x hx i _ j _ => (hsupport x hx).2.1 i (e.symm (.inl j)))
    (fun x hx i c => (hsupport x hx).2.1 i (e.symm (.inr c))) hV hsets hsetsp hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hSS hdel hmass hdelbase hout hdelout
    c₀ hsub hretain hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues
    (fun _ _ _ _ x hx _ => (hsupport x hx).2.2.1)
    (fun _ _ _ _ x hx _ => (hsupport x hx).2.2.2.1)
    (fun _ _ _ _ x hx _ => (hsupport x hx).2.2.2.2)
    houtcover hinjp hrp hspecN hfreqN hQ.1 hQ.2 huBig hrBig hNfreq hEup hαup hβup hVeq
    hUlog hUup hdata'

end Ostmann

end OAI
