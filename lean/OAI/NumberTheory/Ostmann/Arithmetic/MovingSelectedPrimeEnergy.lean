import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeSelectedPriors
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalEnergyRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternEnumeration

namespace OAI

/-! # The actual coefficient energy under selected harmonic prime laws -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The Section 7 energy estimate with its original prime-pattern premise
fully supplied by the published progression estimate and the concrete cells. -/
theorem PublishedProgressionInput.moving_selected_prime_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1 + 1) ≤ (k : ℝ) ^ 3) :
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
        (uG vG rG sG : ℝ),
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
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 →
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
      Real.exp ((49 / 1000 : ℝ) * L) ≤ uG → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
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
      ‖∑ a : transferFrequencyRange (V n), ∑ z : B → primes, ((∏ b, ν b (z b) : ℝ) : ℂ) *
        complexPrimeInterval 1 0 rG sG (fun y => complexPrimeInterval 1 0 uG vG (fun x =>
          (‖movingFrequencyCoefficient (fun q : primes => (q : ℕ)) outside μ childBound pivotBound V
            (movingOriginalLeaf (fun q : primes => (q : ℕ)) p (fun {_} _ => f)
              (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
            φ G n a.val (treeLeafMap (List.map z) n small)
            (treeLeafMap (List.map z) n (bulkSlotLeaves n m slot))
            ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊‖ ^ 2 : ℂ)))‖ ≤
        Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCprior : 1 ≤ K + 1 := (selected_harmonic_family_bounds c K hc hK).1
  filter_upwards [P.movingPattern_prime_selected_priors_rate C hM ψ n r₀ k
    A Wwin Bφ Dφ c K hA hWwin hc hK hBφ hDφ,
    movingFrequencyCoefficient_original_pattern_rate ψ n k hk hn Bφ A (K + 1) ε
      hA hCprior hε hdepth] with L hprime henergy
  dsimp only
  dsimp only at henergy
  obtain ⟨D, hD, hdiv, henergy⟩ := henergy
  intro B _ tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets
    primeLo cutoff tier X Δ hi φ G small slot global Qμ Qν uG vG rG sG
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hsmall hB hsmallLen
    hm hp hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let j₀ : TreeLeafIndex n × Fin (spectatorBulkCount k L) :=
    ⟨Classical.choice inferInstance, ⟨0, hm⟩⟩
  obtain ⟨N, e, hNcard⟩ := movingPattern_enumeration B (slot j₀) n
  have hdel' (s) : ((global.card + (N s + 1) + outside.length : ℕ) : ℝ) ≤
      Real.exp ((K + 1) * L) := by
    exact (Nat.cast_le.mpr (Nat.add_le_add_right
      (Nat.add_le_add_left (hNcard s) global.card) outside.length)).trans hdel
  apply henergy primes (Fin (spectatorBulkCount k L)) B p (fun q : primes => (q : ℕ)) outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j => primeSubsetPrior primes (Qν j))
    childBound pivotBound V (fun {_} _ => f) (fun i => normalizedResidueTransform (sets i))
    Dq Finset.univ X Δ hi φ G small (bulkSlotLeaves n _ slot) uG vG rG sG N e hV
    (fun _ _ => hf0) hcard hVn hV0
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
    uG vG rG sG huG hrG huvG hrsG hvG hsG (fun _ => hsmall) hB (fun _ => hsmallLen)
    rfl hS hN (fun _ a _ => hf a) hD hdiv' hm hp hsets hsetsp hpupper
    hφ hlip hφout hShell (hdel' s) hout hν hμP hνP hμmass hνmass hμrange hνrange
    houtcover hinjp huBig hrBig hVn hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband
    hdeleteμ hdeletep
  calc
    _ ≤ _ := hh
    _ = _ := by
      rw [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin]
      ring

end Ostmann

end OAI
