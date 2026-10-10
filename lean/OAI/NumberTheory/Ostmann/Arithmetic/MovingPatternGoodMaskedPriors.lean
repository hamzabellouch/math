import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGoodMaskedShell
import OAI.NumberTheory.Ostmann.Construction.HarmonicFamilyBounds
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyModelRange
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyModelPage

namespace OAI

/-! # The original diagonal bound for actual selected harmonic laws -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_good_selected_masked_priors_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ c K gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hc : 0 < c) (hK : 0 ≤ K)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cmass := K + 1
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) (n + 2)) (Nfreq : ℕ)
        (small : TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (Qμ : ℕ → Finset ℕ) (Qν : Bidx → Finset ℕ)
        (active : Fin (movingPatternRegularSlots e (n + 2) m small slot).length → Bool)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let Eprior := Real.exp (Cmass * L)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots (n + 2) ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, (n + 2) ≤ tierB i) →
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
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active j = false →
        (movingPatternRegularSlots e (n + 2) m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      (∀ j, j < (n + 2) → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
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
          Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
          (Real.exp (-gain * m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  have hfamily := selected_harmonic_family_bounds c K hc hK
  let Cmass := K + 1
  have hCmass : 1 ≤ Cmass := hfamily.1
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hmain⟩ :=
    P.movingPattern_good_masked_whole_shell_rate C hM ψ n r₀ k A Wwin Bφ Dφ Cmass gain
      hA hWwin hCmass hBφ hDφ
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hmain, movingFrequencyModel_bulk_range (n + 2) k A hA,
    eventually_ge_atTop (max 1 (-Real.log c))] with L hrate hmod hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ N e tierB t Sfreq ft Nfreq small slot perm pattern rep
    primes hprimes _ childBound pivotBound f outside p _ Dq sets β
    primeLo cutoff tier X j₀ φ G global Qμ Qν active sreg setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen ht hS hN hf hm hp
    hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange hactive houtcover hinjp huBig hrBig
    hNfreq hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsreg hsregN hsetsReg
  let μ := fun j => primeSubsetPrior primes (Qμ j)
  let ν := fun j => primeSubsetPrior primes (Qν j)
  let α := Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L))
  let βint := Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L))
  let Vint := Real.exp ((1 / 100 : ℝ) * L)
  let Uall := Real.exp (Real.exp ((11 / 1000 : ℝ) * L))
  obtain ⟨hμ0, hν0, hμsum, hνsum, hμbound, hμα, hνα, hμβ, hμmin⟩ :=
    hfamily.2 L hL primes Bidx Qμ Qν hμP hνP hμmass hνmass hμrange hνrange
  have htiers := selected_harmonic_family_tiers primes Bidx (n + 2) Qμ Qν tier tierB hμtier hνtier
  have hL0 : 0 ≤ L := le_trans (by norm_num) ((le_max_left _ _).trans hL)
  have hμlo (j) (q : primes) (hq : μ j q ≠ 0) : primeLo < (q : ℕ) := by
    have hr := hμmin j q hq
    have hh : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
        Real.exp (Real.exp ((1 / 100 : ℝ) * L)) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hL0]))
    exact_mod_cast (hloReal.trans_le (hh.trans hr))
  have hνlo (j) (q : primes) (hq : ν j q ≠ 0) : primeLo < (q : ℕ) := by
    exact_mod_cast (hloReal.trans_le (hνrange j q (primeSubsetPrior_support primes (Qν j) q hq)))
  have hUlog : Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
    dsimp only [Uall]
    rw [Real.log_exp]
    exact Real.exp_le_exp.mpr (by linarith only [hL0])
  have hUup : Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    exact Real.exp_le_exp.mpr (by simpa only [Uall, Real.log_exp] using hUlog)
  obtain ⟨hrpos, hMpos, hcop, hMQ⟩ := hmod Sfreq Nfreq ft p hS hN hNfreq
    (fun i => Fact.out) hinjp (fun i => hNcut.trans_le (hpband i).1) hpupper
  let : NeZero (frequencyModelBase Sfreq (n + 2) ft ^ ((n + 2) - 1 + 2)) := ⟨Nat.ne_of_gt hrpos⟩
  let : NeZero (∏ i, bulkResidueModuli (frequencyModelBase Sfreq (n + 2) ft ^ ((n + 2) - 1 + 2)) p i) :=
    ⟨Nat.ne_of_gt hMpos⟩
  have hpage := frequencyModel_bulk_page_projection Sfreq (n + 2) Nfreq cutoff ft
    (fun s hs => ⟨hS s hs, hN s hs⟩) hNcut p (selectedPageZero P (bulkProgressionCutoff L))
    (fun i => ⟨Fact.out, (hpband i).1⟩)
    (fun z hz q hq i => (hdeletebulk z hz q hq i).symm)
  by_cases htier : ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2
  ·
    exact hrate lo hi hlo hhi hwindow Bidx Cidx N e tierB (fun c => movingSampleTier (rep c).val.2) t Sfreq ft Nfreq
      small slot perm pattern rep primes hprimes childBound pivotBound f outside p hcop Dq sets β
      primeLo cutoff tier X j₀ φ G global μ ν active (Real.exp (Cmass * L)) α βint Vint Uall sreg setsReg Jleft Jright diagonal uG vG rG sG center
      huG hrG huvG hrsG hvG hsG hvcenter hsmall hB htier hsmallLen ht hS hN hf hm hp
      hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hMQ hpage hφ hlip hφout hShell hdel hout
      (fun j => congrArg (primeSubsetPrior primes) (hν j))
      hμ0 hν0 hμsum hνsum (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith only [hCmass]) hL0))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _) (Real.one_le_exp_iff.mpr (Real.exp_pos _).le)
      hμbound hμα hνα (fun c => hμβ _) (fun c => hμmin _) hupper hactive houtcover hinjp huBig hrBig
      hNfreq le_rfl le_rfl le_rfl rfl hUlog hUup htiers.1 htiers.2 hNlo hNcut hcutlo hμlo hνlo
      hupper hpband
      (fun z hz q hq j a ha heq => hdeleteμ z hz q hq j
        (heq ▸ primeSubsetPrior_support primes (Qμ j) a ha)) hdeletep
      (fun z hz q hq j a ha heq => hdeleteν z hz q hq j
        (heq ▸ primeSubsetPrior_support primes (Qν j) a ha)) hsreg hsregN hsetsReg
  · have hz (H : (Fin (N + 1) → primes) → ℂ) (x) :
        movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern H x = 0 :=
      movingPattern_zero_of_inconsistent_tiers e μ ν (fun q : primes => (q : ℕ))
        pattern rep tier htiers.1 htier H x
    dsimp only [μ, ν] at hz
    simp only [hz, Finset.sum_const_zero, norm_zero]
    positivity

end Ostmann

end OAI
