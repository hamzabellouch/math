import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGoodSelectedPriors
import OAI.NumberTheory.Ostmann.Arithmetic.MovingMatchedCorrelationRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternEnumeration

namespace OAI

/-! # The complete good-matching correlation under original selected harmonic priors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_good_correlation
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k)
    (A Wwin Bφ Dφ c K gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (B : Type) [Fintype B] (tierB : B → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (small : TreeLeafTuple (List B) (n + 2)) (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ B)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ 1) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i ∈ flattenMovingSlots (n + 2) small, i ∉ Set.range slot) →
      (∀ i, (n + 2) ≤ tierB i) → MovingLeafLengthLE (n + 2) small r₀ →
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
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card B + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < (n + 2) → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingOriginalMatchedCorrelation p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
        ψ X (Real.exp Δ) hi φ G (n + 2) small (movingPatternBulkLeaves (n + 2) m slot perm)
        (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center‖ ≤
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCprior : 1 ≤ K + 1 := (selected_harmonic_family_bounds c K hc hK).1
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hprime⟩ :=
    P.movingPattern_good_selected_priors_rate C hM ψ n r₀ k A Wwin Bφ Dφ c K
      (goodPatternGain (n + 2) (K + 1) A gain) hA hWwin hc hK hBφ hDφ
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hprime, movingOriginalMatchedCorrelation_pattern_rate ψ (n + 2) k hk
    A (K + 1) gain hA hCprior] with L hprime hcorr
  dsimp only at hcorr ⊢
  intro B _ tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G small slot perm global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV hf0 hf hcard hVn hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen
    hm hp hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex (n + 2))
  let j₀ : TreeLeafIndex (n + 2) × Fin (spectatorBulkCount k L) :=
    ⟨Classical.choice inferInstance, ⟨0, by omega⟩⟩
  obtain ⟨N, e, hNcard⟩ := movingPattern_enumeration B (slot j₀) (n + 2)
  have hdel' (s) : ((global.card + (N s + 1) + outside.length : ℕ) : ℝ) ≤
      Real.exp ((K + 1) * L) := by
    exact (Nat.cast_le.mpr (Nat.add_le_add_right
      (Nat.add_le_add_left (hNcard s) global.card) outside.length)).trans hdel
  apply hcorr B primes hprimes p
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j => primeSubsetPrior primes (Qν j))
    childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq
    X Δ hi φ G small slot perm (normalizedResidueFamily setsReg) outside Jleft Jright diagonal
    uG vG rG sG center N e hV hf0 hcard
  intro s t
  let rep : ∀ c : Quotient s, {i : Bool × MovingSampleIndex (n + 2) // Quotient.mk'' i = c} :=
    fun c => ⟨c.out, Quotient.out_eq' c⟩
  have hS : ∀ a ∈ Sfreq, a ≠ 0 := fun a ha => (Finset.mem_erase.mp ha).1
  have hN : ∀ a ∈ Sfreq, a.natAbs ≤ V (n + 2) := by
    intro a ha
    exact (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp ha).2
  have hh := hprime (Real.exp Δ) hi (Real.one_le_exp_iff.mpr hΔ) hhi hwindow
    B (Quotient s) (N s) (e s) tierB
    (fun b => frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) b t))
    Sfreq t (V (n + 2)) small slot perm (fun i => Quotient.mk'' i) rep primes hprimes
    childBound pivotBound f outside p Dq sets β primeLo cutoff tier X j₀ φ G global Qμ Qν
    (frequencyRoot (n + 2) (frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) false t)))
    setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter (fun _ => hsmall) hB (fun _ => hsmallLen)
    rfl hS hN hf hm hp hsets hsetsp hpupper hgood hdlo hdhi hβ hbias
    hφ hlip hφout hShell (hdel' s) hout hν hμP hνP hμmass hνmass hμrange hνrange
    houtcover hinjp huBig hrBig hVn hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband
    hdeleteμ hdeletep hdeleteν hdeletebulk
    (hS _ (allFrequencyList_subtype_mem Sfreq (n + 2) (frequencyPairProjection Sfreq (n + 2) false t) _
      (frequencyRoot_mem_allFrequencyList (n + 2) _)))
    (hN _ (allFrequencyList_subtype_mem Sfreq (n + 2) (frequencyPairProjection Sfreq (n + 2) false t) _
      (frequencyRoot_mem_allFrequencyList (n + 2) _))) hsetsReg
  simpa only [add_assoc] using hh

end Ostmann

end OAI
