import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedInitialAmplitudeEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalLeafMultiplier
import OAI.NumberTheory.Ostmann.Construction.InitialMovingHarmonicCost
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport

namespace OAI

/-! # The original diagonal with the retained-log arithmetic saving -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_amplitude_diagonal
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n + 2 < k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d rinit : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd btop : ℝ) (lower : TreeLeafIndex (n + 2) × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let H := G ((n + 2) + 1)
      let slot := movingTemplateBulk (n + 2) r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      4 + r + 4 * (n + 2) = rinit + rinit →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ H - 1 →
      (∀ i, (n + 2) ≤ tierB i) →
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
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) (4 + r) m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j, j ≤ n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
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
      (∀ q ∈ Qμ (n + 2), (q : ℝ) ≤ Real.exp btop) →
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex (n + 2) × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → V (n + 2) < (q : ℕ)) →
      (∀ q : smoothGiantPrimeRange H, smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0 →
        ∀ j (z : primes), (z : ℕ) ∈ Qν j → (q : ℕ) ≠ (z : ℕ)) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (2 * cb - 2))) *
        ((Fintype.card (MovingRegularSlot (n + 2) r m)).factorial : ℝ) *
        (∏ i, (∑ q ∈ Qν i, (q : ℝ)⁻¹)⁻¹)) *
      (Real.exp (((2 ^ (n + 2) * 4 : ℕ) : ℝ) * btop +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
      (4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, henergy⟩ :=
    P.moving_selected_initial_amplitude_energy C hM ψ n r k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (0 : ℝ)] with L henergy hL
  intro b hsize
  have henergy := henergy b hsize
  dsimp only at henergy ⊢
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hsep
  have he := henergy tierB primes hprimes d rinit sl sr fallback childBound pivotBound V outside p Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd btop
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb
  let m := b + b
  let depth := n + 2
  let H := G (depth + 1)
  have hVbound : (V depth : ℝ) ≤ Real.exp (H - 1) := by
    apply (Nat.cast_le.mpr hNlo).trans
    apply hloReal.le.trans
    apply Real.exp_le_exp.mpr
    apply le_trans (Real.exp_le_exp.mpr _) hHbig
    nlinarith only [hL]
  have hvg (q : smoothGiantPrimeRange H)
      (hq : smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0) : V depth < (q : ℕ) := by
    have hq' := (smoothGiantPrior_active_bounds _ (smoothGiantPrimeRange_prime H) φ H hφout q hq).1
    exact_mod_cast hVbound.trans_lt hq'
  have hX (q : smoothGiantPrimeRange H)
      (hq : smoothGiantPrior (smoothGiantPrimeRange H) φ H q ≠ 0) :
      Real.exp (H - 1) ≤ (q : ℝ) :=
    (smoothGiantPrior_active_bounds _ (smoothGiantPrimeRange_prime H) φ H hφout q hq).1.le
  have hcost := movingAmplitude_initial_full_harmonic_cost primes
    (smoothGiantPrimeRange H) (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
    hprimes (smoothGiantPrimeRange_prime H) b d rinit cb cd sl sr fallback
    p (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi
    outside (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a)
    childBound pivotBound V φ hφpos hφ1 G depth r hlen Qν
    (fun j l => by rw [hν j, hν l]) hvg
    (fun j q hq => hvr j q (primeSubsetPrior_support _ _ q hq))
    (fun q hq j z hz => hsep q hq j z (primeSubsetPrior_support _ _ z hz))
    (H - 1) hX lower (fun j q hq => hlower j q (primeSubsetPrior_support _ _ q hq))
    (normalizedResidueFamily setsReg) ggiant favorable
  dsimp only at hcost
  apply hcost.trans
  apply mul_le_mul_of_nonneg_left he
  apply mul_nonneg
  · exact mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr
      (Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))))

end Ostmann

end OAI
