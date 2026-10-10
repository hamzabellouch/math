import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternDiagonalSharp
import OAI.NumberTheory.Ostmann.Arithmetic.WholeShellArithmeticCells
import OAI.NumberTheory.Ostmann.Construction.FrozenPrimeDeletions

namespace OAI

/-! # The original mixed diagonal bound on the entire bulk shell -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_diagonal_whole_shell_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
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
        (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
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
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
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
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
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
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j a, ν j a ≠ 0 → (a : ℕ) ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e n m small slot).get (fun _ => true) sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          (Real.exp (Cmass * L)) ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
          (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
              Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) *
                2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  filter_upwards [P.movingPattern_original_diagonal_sharp ψ n r₀ k
    A Wwin Bφ Dφ Cmass Cmass hA hWwin hCmass hBφ hDφ hCmass,
    whole_shell_arithmetic_cells C Cmass hM hCmass] with L hrate hcells
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ N e tierB tierC t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound f outside _ p _ hc _ Dq sets
    primeLo cutoff tier X j₀ φ G global μ ν Eprior αall βint Vint Uall sreg setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp
    hsets hsetsp hpupper hMQ hφ hlip hφout hShell hdel hout hν
    hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues houtcover hinjp huBig hrBig
    hNfreq hEup hαup hβup hVeq hUlog _hUup hμtier hνtier hNlo hNcut hcutlo hμlo hνlo
    hupper hpband hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  let m := spectatorBulkCount k L
  let a : ℝ := (4 / 1000) * L
  let b : ℝ := (6 / 1000) * L
  let u := fun (_ : TreeLeafIndex n × Fin m) => wholeShellLower a b
  let v := fun (_ : TreeLeafIndex n × Fin m) => wholeShellUpper a b
  let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq n ft) ^ (n - 1 + 2)) p i
  let S := primeLogCellSet 1 0 (Real.exp a) (Real.exp b)
  let deleted := fun x : Fin (N + 1) → primes => global ∪
    frozenPrimeDeletions (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot) outside
  obtain ⟨hcard, hunit, hlow, huv, hshort, hsep, hMcell, hsupport, hmass⟩ :=
    hcells M hMQ
  have hDcard (x) : ((deleted x).card : ℝ) ≤ Real.exp (Cmass * L) := by
    have hh : (deleted x).card ≤ global.card + (N + 1) + outside.length := by
      have ht := (Finset.card_union_le global _).trans
        (Nat.add_le_add_left (frozenPrimeDeletions_card_le
          (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot) outside) global.card)
      simpa only [Fintype.card_fin, Nat.add_assoc] using ht
    exact (Nat.cast_le.mpr hh).trans hdel
  have hsub (j) : S \ global ⊆ primeCellSupport M
      (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) := by
    rw [hsupport]; exact Finset.sdiff_subset
  have hretain (x) (j) :
      primeCellSupport M (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1) \ deleted x ⊆ S \ global := by
    rw [hsupport]
    intro q hq
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1,
      fun hg => (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_left _ hg)⟩
  have hmem (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s ∈ Sfreq := by
    rw [ht] at hs
    exact allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n b ft) s hs
  have hfreq (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) : s ≠ 0 :=
    hS s (hmem b s hs)
  have hV (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList n (t b)) :
      |(s : ℝ)| ≤ Real.exp (A * m) := by
    have hn : (s.natAbs : ℝ) ≤ Nfreq := by exact_mod_cast hN s (hmem b s hs)
    exact (show |(s : ℝ)| ≤ Nfreq by simpa only [Nat.cast_natAbs, Int.cast_abs] using hn).trans hNfreq
  exact hrate lo hi hlo hhi hwindow Bidx Cidx (Fin (wholePrimeGridCount b)) N e tierB tierC
    t Sfreq ft Nfreq Vleaf D small slot pattern rep primes hprimes childBound pivotBound hfreq f
    outside p hc Dq sets X j₀ φ G u v (fun x _ => deleted x) (fun _ => S \ global)
    μ ν (fun _ => true) sreg setsReg Jleft Jright diagonal
    Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter (hsmall false) hB htier (hsmallLen false)
    ht hS hN (fun s => hleaf false s []) hD hdiv hm hp hV
    hsets hsetsp hpupper hMQ hφ hlip hφout hcard (fun _ => hunit) (fun _ => hlow)
    (fun _ => huv) (fun _ => hshort) (fun _ => hsep) (fun _ => hMcell)
    (fun j => by dsimp only [u, v]; rw [hsupport]; exact hShell) (fun x _ _ => hDcard x)
    (fun j => by dsimp only [u, v]; rw [hsupport]; exact hmass)
    (fun x _ _ i hi => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_base (fun i => (x i : ℕ)) _ outside i hi)) hout
    (fun x _ _ q hq => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_outside (fun i => (x i : ℕ)) _ outside q hq))
    (⟨0, wholePrimeGridCount_pos b⟩, 1) hsub (fun x _ => hretain x) hν
    hμ0 hν0 hμmass hνmass (le_trans (by norm_num) hEprior) hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues (fun _ h => by cases h)
    hinjp houtcover hNfreq huBig hrBig tier primeLo cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hpband hdeleteμ hdeletep hdeleteν
    hsreg hsregN hsetsReg hEup hUlog hαup hβup hVeq

end Ostmann

end OAI
