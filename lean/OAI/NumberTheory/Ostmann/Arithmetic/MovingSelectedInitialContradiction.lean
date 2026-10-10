import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedInitialFinalStatistic
import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedFinalRate

namespace OAI

/-! # Contradiction at the last depth for the actual initial half-cutoff leaf -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_final_contradiction_varying_window
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (Bs BD Bz B Bφ Dφ c K : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) (hc : 0 < c) (hK : 0 ≤ K)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∀ᶠ k : ℕ in atTop, ∀ Wwin : ℝ, 0 ≤ Wwin → 8 * (K + 1) ≤ (k : ℝ) ^ 3 →
    let A := movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot k 6 m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot k 6 m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (H cb cd : ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let slot := movingTemplateBulk k 6 m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V k)).erase 0
      6 + 4 * k = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V k : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, k ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot k 6 m) + 4 * k * 2 ^ k) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j < k → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V k ≤ primeLo → V k < cutoff → cutoff ≤ primeLo →
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
      smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H ≤ L →
      Real.exp (-B * (2 : ℝ) ^ k * m) ≤
        ‖movingTemplatePrimeAmplitude Subtype.val outside μ childBound pivotBound V
          (movingOriginalLeaf Subtype.val p
            (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
            (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
          φ G k 6 m (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
          ν (normalizedResidueFamily setsReg) ggiant favorable‖ → False := by
  filter_upwards [eventually_moving_normalized_numeric_contradiction Bs BD Bz B
    (diagonalOuterMajorant Bφ Dφ false) (diagonalOuterMajorant_pos Bφ Dφ false).le,
    eventually_ge_atTop (2 : ℕ)] with k hnumeric hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  intro Wwin hWwin hdepth A
  have hk0 : 0 < (n + 2) := by omega
  have hA : 0 ≤ A := by
    dsimp only [A, movingFrequencyRate]
    have hlog : 0 ≤ Real.log (((n + 2 : ℕ) : ℝ) ^ 4) := Real.log_nonneg
      (one_le_pow₀ (show (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) by exact_mod_cast hk0) )
    have hlogr : 0 ≤ Real.log ((2 : ℝ) ^ (n + 2)) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    exact mul_nonneg (by positivity) (by nlinarith [mul_nonneg hBz hlog])
  let gain := A + (2 * (B + 1) + 1) * (2 : ℝ) ^ (n + 2) + 1
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, he⟩ :=
    P.moving_selected_initial_final_statistic C hM ψ n 6 (n + 2) hk0 (by omega)
      A Wwin Bφ Dφ c K 1 gain hA hWwin hBφ hDφ hc hK (by norm_num) hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [he, hnumeric] with L he hnumeric
  intro b hsize
  have he := he b hsize
  dsimp only at he ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg H cb cd ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔbound hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig hμtier hνtier
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
    hcg hlower
  have hstat := he tierB primes hprimes d r sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg H cb cd ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig hμtier hνtier
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hid := movingTemplatePrimeAmplitude_statistic_eq primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ hφout G (n + 2) 6 (b + b) (fun j => primeSubsetPrior primes (Qν j))
    (normalizedResidueFamily setsReg) ggiant favorable H
  have hmcast : (spectatorBulkCount (n + 2) L : ℝ) = (b + b : ℕ) := by exact_mod_cast hsize
  have hf := hnumeric (V (n + 2)) (by simpa only [hmcast] using hVn) hA Δ
    (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H)
    (by simpa only [hmcast, spectatorBaseGap] using hΔbound) hcg _ _ hid
    (by simpa only [hmcast] using hlower)
  apply hf
  simpa only [hmcast, gain, A, Nat.cast_pow, Nat.cast_ofNat, one_mul, mul_assoc, add_assoc] using hstat

end Ostmann

end OAI
