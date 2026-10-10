import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternDiagonalSelectedPriors
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalEnergyRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternEnumeration

namespace OAI

/-! # The actual mixed diagonal energy under selected harmonic prime laws -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The mixed diagonal energy estimate with its original arithmetic premise
fully supplied by the published progression estimate and the concrete cells. -/
theorem PublishedProgressionInput.moving_selected_diagonal_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (B : Type) [Fintype B] (tierB : B → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → MovingLeafLengthLE n small r₀ →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card B + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingOriginalDiagonalEnergy p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
        ψ X (Real.exp Δ) hi φ G n small (bulkSlotLeaves n m slot)
        (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center‖ ≤
        Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCprior : 1 ≤ K + 1 := (selected_harmonic_family_bounds c K hc hK).1
  filter_upwards [P.movingPattern_diagonal_selected_priors_rate C hM ψ n r₀ k
    A Wwin Bφ Dφ c K hA hWwin hc hK hBφ hDφ,
    movingOriginalDiagonalEnergy_pattern_rate ψ n k hk hn Bφ A (K + 1) ε
      hA hCprior hε hdepth] with L hprime henergy
  dsimp only
  dsimp only at henergy
  obtain ⟨D, hD, hdiv, henergy⟩ := henergy
  intro B _ tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets
    primeLo cutoff tier X Δ hi φ G small slot global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen
    hm hp hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let j₀ : TreeLeafIndex n × Fin (spectatorBulkCount k L) :=
    ⟨Classical.choice inferInstance, ⟨0, hm⟩⟩
  obtain ⟨N, e, hNcard⟩ := movingPattern_enumeration B (slot j₀) n
  have hdel' (s) : ((global.card + (N s + 1) + outside.length : ℕ) : ℝ) ≤
      Real.exp ((K + 1) * L) := by
    exact (Nat.cast_le.mpr (Nat.add_le_add_right
      (Nat.add_le_add_left (hNcard s) global.card) outside.length)).trans hdel
  apply henergy B primes hprimes p
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j => primeSubsetPrior primes (Qν j))
    childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq
    X Δ hi φ G small slot (normalizedResidueFamily setsReg) outside Jleft Jright diagonal
    uG vG rG sG center N e hV hf0 hcard hVn hV0
  intro s t
  let rep : ∀ c : Quotient s, {i : Bool × MovingSampleIndex n // Quotient.mk'' i = c} :=
    fun c => ⟨c.out, Quotient.out_eq' c⟩
  have hS : ∀ a ∈ Sfreq, a ≠ 0 := fun a ha => (Finset.mem_erase.mp ha).1
  have hN : ∀ a ∈ Sfreq, a.natAbs ≤ V n := by
    intro a ha
    exact (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp ha).2
  have hdiv' (q : ℕ) (hq : q ≠ 0) (hsize : q ≤ (V n) ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ ((V n : ℕ) : ℝ) ^ 2 := by exact_mod_cast hsize
      _ ≤ (Real.exp (A * spectatorBulkCount k L)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hVn 2
      _ = Real.exp (2 * A * spectatorBulkCount k L) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hh := hprime (Real.exp Δ) hi (Real.one_le_exp_iff.mpr hΔ) hhi hwindow
    B (Quotient s) (N s) (e s) tierB
    (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b t))
    Sfreq t (V n) (V 0) D small slot (fun i => Quotient.mk'' i) rep primes hprimes
    childBound pivotBound f outside p Dq sets primeLo cutoff tier X j₀ φ G global Qμ Qν
    (frequencyRoot n (frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n false t)))
    setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter (fun _ => hsmall) hB (fun _ => hsmallLen)
    rfl hS hN (fun _ a _ => hf a) hD hdiv' hm hp hsets hsetsp hpupper
    hφ hlip hφout hShell (hdel' s) hout hν hμP hνP hμmass hνmass hμrange hνrange
    houtcover hinjp huBig hrBig hVn hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband
    hdeleteμ hdeletep hdeleteν
    (hS _ (allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n false t) _
      (frequencyRoot_mem_allFrequencyList n _)))
    (hN _ (allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n false t) _
      (frequencyRoot_mem_allFrequencyList n _))) hsetsReg
  calc
    _ ≤ _ := hh
    _ ≤ _ := by
      rw [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin]
      have hw : 0 ≤ frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
          ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod := by
        apply mul_nonneg
        · exact frequencyLeafWeight_nonneg _ (fun _ => by
            unfold pairedFrequencyLeaf
            split_ifs <;> norm_num) n t
        · apply List.prod_nonneg
          intro a ha
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
          exact pairFrequencySupportBound_nonneg D a
      have hκ : 0 ≤ (2 : ℝ) ^ Fintype.card (Quotient s) *
          (Real.exp ((K + 1) * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s)) := by positivity
      have hreserve : 0 ≤
          (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            Bφ ^ (2 ^ n - 1)) ^ 2) *
          ((2 : ℝ) ^ (2 ^ n * spectatorBulkCount k L) * 3 ^ (2 ^ n * spectatorBulkCount k L)) *
          (frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
            ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod) *
          2 ^ (2 ^ n * spectatorBulkCount k L) := by positivity
      nlinarith only [mul_nonneg hκ hreserve]

end Ostmann

end OAI
