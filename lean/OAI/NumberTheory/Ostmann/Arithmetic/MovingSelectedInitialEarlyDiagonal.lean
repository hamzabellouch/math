import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedAmplitudeEnergy
import OAI.NumberTheory.Ostmann.Construction.InitialMovingEarlyEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalLeafMultiplier
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport

namespace OAI

/-! # Original first-step diagonals from the single-assignment arithmetic bound -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_early_log_diagonal
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n < k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, ∀ bsize : ℕ, spectatorBulkCount k L = bsize + bsize →
      let m := bsize + bsize
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi b : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd : ℝ) (lower : TreeLeafIndex n × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G (n + 1)
      let slot := movingTemplateBulk n r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      4 + r + 4 * n = rinit + rinit →
      Monotone V →
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
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex n × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ i (q : primes), (q : ℕ) ∈ Qν i → V n < (q : ℕ)) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val bsize d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G n r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) *
        ((Fintype.card (MovingRegularSlot n r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Qν i, (q : ℝ)⁻¹)⁻¹)) *
      (Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
        (4 * (Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))))) := by
  filter_upwards [P.moving_selected_amplitude_regular_energy C hM ψ n r k hk hn.le
    A Wwin Bφ Dφ c K ε hA hWwin hBφ hDφ hc hK hε hdepth,
    eventually_ge_atTop (0 : ℝ)] with L henergy hL
  intro bsize hsize
  dsimp only at henergy ⊢
  rw [hsize] at henergy
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg cb cd lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb hφ1 hlower hvr
  have he := henergy tierB primes hprimes childBound pivotBound V (movingCompactLeaf (V 0)) outside p Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg
    hV (movingCompactLeaf_zero _) (movingCompactLeaf_norm _) hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb
  let m := bsize + bsize
  let H := G (n + 1)
  have hexp : Real.exp ((11 / 1000 : ℝ) * L) ≤ H - 1 := by
    apply le_trans (Real.exp_le_exp.mpr _) hHbig
    nlinarith only [hL]
  have hPbound (a : primes) : (a : ℝ) ≤ Real.exp (H - 1) :=
    (hupper a).trans (Real.exp_le_exp.mpr hexp)
  have hVbound : (V n : ℝ) ≤ Real.exp (H - 1) := by
    apply (Nat.cast_le.mpr hNlo).trans
    apply hloReal.le.trans
    apply Real.exp_le_exp.mpr
    apply le_trans (Real.exp_le_exp.mpr _) hHbig
    nlinarith only [hL]
  obtain ⟨hvg, hsep⟩ := smoothGiantPrior_active_separation (smoothGiantPrimeRange H) primes
    (smoothGiantPrimeRange_prime H) φ H hφout (V n) hVbound hPbound
  have hX (q : smoothGiantPrimeRange H)
      (hq : smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0) :
      Real.exp (H - 1) ≤ (q : ℝ) :=
    (smoothGiantPrior_active_bounds _ (smoothGiantPrimeRange_prime H) φ H hφout q hq).1.le
  have hcost := movingAmplitude_initial_regular_harmonic_cost primes
    (smoothGiantPrimeRange H) (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
    hprimes (smoothGiantPrimeRange_prime H) bsize d rinit cb cd sl sr fallback p
    (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi
    outside (fun j => primeSubsetPrior primes (Qμ j))
    (fun j a => primeSubsetPrior_nonneg _ _ a) childBound pivotBound V
    φ hφ0 hφ1 G n r hlen Qν lower
    (fun j q hq => hlower j q (primeSubsetPrior_support _ _ q hq))
    hvg (fun i q hq => hvr i q (primeSubsetPrior_support _ _ q hq))
    (fun q hq _ a _ => hsep q hq a) (H - 1) hX
    (normalizedResidueFamily setsReg) ggiant favorable
  have hplain := movingAmplitudeRegularEnergy_initial_le primes
    (smoothGiantPrimeRange H) (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
    bsize d rinit cb cd sl sr fallback p (fun i => normalizedResidueTransform (sets i))
    Dq Finset.univ ψ X (Real.exp Δ) hi outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a)
    childBound pivotBound V φ hφ0 G n r hlen Qν (normalizedResidueFamily setsReg)
  exact hcost.trans (mul_le_mul_of_nonneg_left (hplain.trans he) (by
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
        (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))))))

end Ostmann

end OAI
