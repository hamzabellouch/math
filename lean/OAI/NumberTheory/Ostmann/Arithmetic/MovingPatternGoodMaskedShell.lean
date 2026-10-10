import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGoodSharp
import OAI.NumberTheory.Ostmann.Arithmetic.WholeShellArithmeticCells
import OAI.NumberTheory.Ostmann.Construction.FrozenPrimeDeletions

namespace OAI

/-! # The original mixed diagonal bound on the entire bulk shell -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_good_masked_whole_shell_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ Cmass gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) (n + 2)) (Nfreq : ℕ)
        (small : TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ) [NeZero ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2))]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i).Coprime (bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p j)))
        [NeZero (∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i)]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (active : Fin (movingPatternRegularSlots e (n + 2) m small slot).length → Bool)
        (Eprior αall βint Vint Uall : ℝ)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots (n + 2) ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, (n + 2) ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b : Bool, MovingLeafLengthLE (n + 2) ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ s, ‖f s‖ ≤ 1) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2))
          (selectedPageZero P (bulkProgressionCutoff L)) →
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
      (∀ j, active j = false →
        (movingPatternRegularSlots e (n + 2) m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
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
      (∀ j, j < (n + 2) → ∀ a, μ j a ≠ 0 → tier a = j) →
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
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
        (movingOriginalPatternMatchedObservable e t small slot perm pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e (n + 2) m small slot).get active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e (n + 2) m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          (Real.exp (Cmass * L)) ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
          (Real.exp (-gain * m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hmain⟩ :=
    P.movingPattern_original_good_sharp ψ n r₀ k A Wwin Bφ Dφ 1 Cmass Cmass gain
      hA hWwin (by norm_num) hCmass hBφ hDφ hCmass
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hmain, whole_shell_arithmetic_cells C Cmass hM hCmass] with L hrate hcells
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ N e tierB tierC t Sfreq ft Nfreq small slot perm pattern rep
    primes hprimes _ childBound pivotBound f outside _ p _ hc _ Dq sets β
    primeLo cutoff tier X j₀ φ G global μ ν active Eprior αall βint Vint Uall sreg setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter hsmall hB htier hsmallLen ht hS hN hf hm hp
    hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hMQ hpage hφ hlip hφout hShell hdel hout hν
    hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hactive houtcover hinjp huBig hrBig
    hNfreq hEup hαup hβup hVeq hUlog _hUup hμtier hνtier hNlo hNcut hcutlo hμlo hνlo
    hupper hpband hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  let m := spectatorBulkCount k L
  let a : ℝ := (4 / 1000) * L
  let b : ℝ := (6 / 1000) * L
  let u := fun (_ : TreeLeafIndex (n + 2) × Fin m) => wholeShellLower a b
  let v := fun (_ : TreeLeafIndex (n + 2) × Fin m) => wholeShellUpper a b
  let M := ∏ i, bulkResidueModuli ((frequencyModelBase Sfreq (n + 2) ft) ^ ((n + 2) - 1 + 2)) p i
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
  have hmem (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList (n + 2) (t b)) : s ∈ Sfreq := by
    rw [ht] at hs
    exact allFrequencyList_subtype_mem Sfreq (n + 2) (frequencyPairProjection Sfreq (n + 2) b ft) s hs
  have hfreq (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList (n + 2) (t b)) : s ≠ 0 :=
    hS s (hmem b s hs)
  have hV (b : Bool) (s : ℤ) (hs : s ∈ allFrequencyList (n + 2) (t b)) :
      |(s : ℝ)| ≤ Real.exp (A * m) := by
    have hn : (s.natAbs : ℝ) ≤ Nfreq := by exact_mod_cast hN s (hmem b s hs)
    exact (show |(s : ℝ)| ≤ Nfreq by simpa only [Nat.cast_natAbs, Int.cast_abs] using hn).trans hNfreq
  have hone (side : Bool) :
      ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1)
        (movingPatternFinBulkData e (n + 2) m t (fun _ => small) slot perm pattern side)‖ ≤ 1 :=
    movingDataWeight_unit_norm_le_one _ (fun s _ => hf s) _
  have hamp : 2 * (‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1)
      (movingPatternFinBulkData e (n + 2) m t (fun _ => small) slot perm pattern false)‖ *
    ‖movingDataWeight (fun {_} _ => f) (fun _ _ _ _ => 1)
      (movingPatternFinBulkData e (n + 2) m t (fun _ => small) slot perm pattern true)‖) ≤
      Real.exp (1 * (m : ℝ)) := by
    have hn := mul_le_mul (hone false) (hone true) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have he := Real.add_one_le_exp (1 * (m : ℝ))
    nlinarith only [hn, hmR, he]
  exact hrate lo hi hlo hhi hwindow Bidx Cidx (Fin (wholePrimeGridCount b)) N e tierB tierC
    t Sfreq ft Nfreq small slot perm pattern rep primes hprimes childBound pivotBound hfreq f
    outside p hc Dq sets β X j₀ φ G u v (fun x _ => deleted x) (fun _ => S \ global)
    μ ν active sreg setsReg Jleft Jright diagonal
    Eprior αall βint Vint Uall uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter (hsmall false) hB htier (hsmallLen false)
    ht hS hN hf hm hp hV
    hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hamp hMQ hpage hφ hlip hφout hcard (fun _ => hunit) (fun _ => hlow)
    (fun _ => huv) (fun _ => hshort) (fun _ => hsep) (fun _ => hMcell)
    (fun j => by dsimp only [u, v]; rw [hsupport]; exact hShell) (fun x _ _ => hDcard x)
    (fun j => by dsimp only [u, v]; rw [hsupport]; exact hmass)
    (fun x _ _ i hi => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_base (fun i => (x i : ℕ)) _ outside i hi)) hout
    (fun x _ _ q hq => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_outside (fun i => (x i : ℕ)) _ outside q hq))
    (⟨0, wholePrimeGridCount_pos b⟩, 1) hsub (fun x _ => hretain x) hν
    hμ0 hν0 hμmass hνmass (le_trans (by norm_num) hEprior) hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hactive
    hinjp houtcover hNfreq huBig hrBig tier primeLo cutoff hNlo hNcut hcutlo
    hμtier hνtier hμlo hνlo hupper hpband hdeleteμ hdeletep hdeleteν
    hsreg hsregN hsetsReg hEup hUlog hαup hβup hVeq

end Ostmann

end OAI
