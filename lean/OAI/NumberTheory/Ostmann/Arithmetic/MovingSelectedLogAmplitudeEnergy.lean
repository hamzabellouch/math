import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedTemplateLogFullEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeSymmetrizedNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRestoredTierSeparation

namespace OAI

/-! # The retained-log symmetrized amplitude with its original compensation law -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_log_symmetrized_amplitude_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n + 2 < k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd b : ℝ),
      let H := G ((n + 2) + 1)
      let slot := movingTemplateBulk (n + 2) r m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
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
      (∀ j : TreeLeafIndex (n + 2) × Fin r, tierB (j.1, .inl j.2) ≠ k) →
      (∀ j, tierB (slot j) = k) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ H - 1 →
      (∀ j (q : primes), (q : ℕ) ∈ Qμ j → tier q = j) →
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
      (∀ q ∈ Qμ (n + 2), (q : ℝ) ≤ Real.exp b) →
      movingAmplitudeSymmetrizedRegularEnergy primes (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊) outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r m Qν (normalizedResidueFamily setsReg) ≤
      Real.exp (((2 ^ (n + 2) * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) *
      (4 * ((((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)))) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, henergy⟩ :=
    P.moving_selected_template_log_full_energy C hM ψ n (4 + r) k hk hn.le
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (0 : ℝ)] with L henergy hL
  dsimp only at henergy ⊢
  intro tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G global Qμ Qν setsReg cb cd b
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange hsmalltier hbulktier houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb
  let m := spectatorBulkCount k L
  let d := n + 2
  let Qfull := movingRestoredPrimeSets d r m (Qμ d) Qν
  have hall (R : Finset ℕ → Prop) (h0 : R (Qμ d)) (h1 : ∀ j, R (Qν j)) : ∀ j, R (Qfull j) := by
    intro j
    dsimp only [Qfull, movingRestoredPrimeSets]
    cases (movingReverseTemplate d r m).symm j with
    | inl _ => exact h0
    | inr j => exact h1 j
  have hlow : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    linarith
  have he := henergy (movingRestoredTiers d r m tierB) primes hprimes
    childBound pivotBound V f outside p Dq sets β primeLo cutoff tier X Δ hi φ G
    (movingRestoredActive d r m) global Qμ Qfull setsReg (G (d + 1)) cb cd
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow hH (movingRestoredTiers_lower d r m tierB hB)
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout
    (fun j => by simpa only [Qfull, m, d, movingRestoredPrimeSets_bulk] using hν j)
    hμP (hall (fun Q => Q ⊆ primes) (hμP d) hνP) hμmass
    (hall (fun Q => c / Real.exp (K * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹) (hμmass d) hνmass)
    hμrange
    (hall (fun Q => ∀ q ∈ Q, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ))
      (fun q hq => hlow.trans (hμrange d q hq)) hνrange)
    (movingRestoredActive_bulk d r m)
    (movingRestoredTiers_small d r m k hn.ne tierB hsmalltier)
    (movingRestoredTiers_bulk d r m k tierB hbulktier)
    houtcover hinjp hHbig hμtier
    (movingRestoredPrimeSets_tier primes d r m (Qμ d) Qν tierB tier (hμtier d) hνtier)
    hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep
    (fun z hz q hq => hall (fun Q => q ∉ Q) (hdeleteμ z hz q hq d) (hdeleteν z hz q hq))
    hdeletebulk hsetsReg
  have hnrm := movingAmplitudeSymmetrizedRegularEnergy_norm_le primes hprimes outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j a => primeSubsetPrior_nonneg _ _ a) d r m
    childBound pivotBound V
    (movingOriginalLeaf Subtype.val p
      (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
      (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
    φ hφpos hφout G Qν (normalizedResidueFamily setsReg) (G (d + 1)) b
    (fun a ha => hb a (primeSubsetPrior_support _ _ a ha))
  dsimp only at hnrm
  rw [← movingRestoredPrimeSets_prior primes d r m (Qμ d) Qν] at hnrm
  exact hnrm.trans (mul_le_mul_of_nonneg_left he (Real.exp_nonneg _))

end Ostmann

end OAI
