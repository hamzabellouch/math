import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedFullEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeOriginalEnergyNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredPrimeLaws

namespace OAI

/-! # The published arithmetic estimate for the actual one-branch energy -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_amplitude_regular_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi b : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q)),
      let H := G (n + 1)
      let slot := movingTemplateBulk n r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, n ≤ tierB i) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
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
      (∀ q ∈ Qμ n, (q : ℝ) ≤ Real.exp b) →
      movingAmplitudeRegularEnergy primes (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊) outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p (fun _ => f) (fun i => normalizedResidueTransform (sets i))
          Dq Finset.univ ψ X (Real.exp Δ) hi) φ G n r m Qν (normalizedResidueFamily setsReg) ≤
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
        (4 * (Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) := by
  filter_upwards [P.moving_selected_template_full_diagonal_energy C hM ψ n (4 + r) k hk hn
    A Wwin Bφ Dφ c K ε hA hWwin hBφ hDφ hc hK hε hdepth,
    eventually_ge_atTop (0 : ℝ)] with L henergy hL
  dsimp only
  dsimp only at henergy
  intro tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb
  let m := spectatorBulkCount k L
  let Qfull := movingRestoredPrimeSets n r m (Qμ n) Qν
  have hall (R : Finset ℕ → Prop) (h0 : R (Qμ n)) (h1 : ∀ j, R (Qν j)) : ∀ j, R (Qfull j) := by
    intro j
    dsimp only [Qfull, movingRestoredPrimeSets]
    cases (movingReverseTemplate n r m).symm j with
    | inl _ => exact h0
    | inr j => exact h1 j
  have hlow : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  have he := henergy (movingRestoredTiers n r m tierB) primes hprimes
    childBound pivotBound V f outside p Dq sets primeLo cutoff tier X Δ hi φ G
    (movingRestoredActive n r m) global Qμ Qfull setsReg (G (n + 1))
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow hH (movingRestoredTiers_lower n r m tierB hB)
    hm hp hsets hsetsp hpupper hφ hlip hφout hShell hdel hout
    (fun j => by simpa only [Qfull, m, movingRestoredPrimeSets_bulk] using hν j)
    hμP (hall (fun Q => Q ⊆ primes) (hμP n) hνP) hμmass
    (hall (fun Q => c / Real.exp (K * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹) (hμmass n) hνmass)
    hμrange
    (hall (fun Q => ∀ q ∈ Q, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ))
      (fun q hq => hlow.trans (hμrange n q hq)) hνrange)
    (movingRestoredActive_bulk n r m) houtcover hinjp hHbig
    (fun j hj => hμtier j hj.le)
    (movingRestoredPrimeSets_tier primes n r m (Qμ n) Qν tierB tier (hμtier n le_rfl) hνtier)
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep
    (fun z hz q hq => hall (fun Q => q ∉ Q) (hdeleteμ z hz q hq n) (hdeleteν z hz q hq)) hsetsReg
  have hnrm := movingAmplitudeRegularEnergy_original_norm_le primes hprimes p outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a) n r m
    childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
    ψ X (Real.exp Δ) hi φ hφ0 hφout G Qν (normalizedResidueFamily setsReg) (G (n + 1)) b
    (fun a ha => hb a (primeSubsetPrior_support _ _ a ha))
  dsimp only at hnrm
  rw [← movingRestoredPrimeSets_prior primes n r m (Qμ n) Qν] at hnrm
  exact hnrm.trans (mul_le_mul_of_nonneg_left he (Real.exp_nonneg _))

end Ostmann

end OAI
