import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedLogDiagonal
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalBudget

namespace OAI

/-! # Decay of the original selected diagonal from its explicit cell-gap inequality -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_log_diagonal_decay
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n + 2 < k)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : 4 * (K + 1) * r ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (cb cd b : ℝ) (lower : TreeLeafIndex (n + 2) × Fin r → ℝ)
        (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool),
      let Δ := spectatorBaseGap Bs ((k : ℝ) ^ 4) m
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
      (∀ x, φ x ≤ 1) →
      (∀ j : TreeLeafIndex (n + 2) × Fin r, ∀ q : primes,
        (q : ℕ) ∈ Qν (j.1, .inl j.2) → Real.exp (lower j) ≤ (q : ℝ)) →
      (∀ q : primes, V (n + 2) < (q : ℕ)) →
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ (n + 2) * 4 : ℕ) : ℝ) * b -
          ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (cb - 1)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ (n + 2) : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ (n + 2) : ℕ) * m) := by
  let gain := max 0 ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) +
    Real.log (2 ^ (n + 2) : ℕ) + 1 + 2 * B + 6) * (2 ^ (n + 2) : ℕ))
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hdiag⟩ :=
    P.moving_selected_log_amplitude_diagonal C hM ψ n r k hk hn
      A Wwin Bφ Dφ c K εdiag gain hA hWwin hBφ hDφ hc hK hεdiag hdepth Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  have hnumeric := selected_diagonal_budget hM (n + 2) r k hk c K Bs BD Bz B 1 εdiag
    hc hK hBs hBD0 (by norm_num) hεdiag.le (by simpa only [one_mul] using hmassBudget) hBz hBD
  filter_upwards [hdiag, hnumeric] with L hdiag hnumeric
  dsimp only at hdiag hnumeric ⊢
  intro tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets β
    primeLo cutoff tier X hi φ G global Qμ Qν setsReg cb cd b lower ggiant favorable
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange hsmalltier hbulktier houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr hgap
  have he := hdiag tierB primes hprimes childBound pivotBound V f outside p Dq sets β
    primeLo cutoff tier X (spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)) hi φ G global Qμ Qν setsReg cb cd b lower ggiant favorable
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange hsmalltier hbulktier houtcover hinjp hHbig
    hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν
    hdeletebulk hsetsReg hb hφ1 hlower hvr
  let m := spectatorBulkCount k L
  let H := G ((n + 2) + 1)
  let arch := Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
    ((2 ^ (n + 2) * 4 : ℕ) : ℝ) * b -
      ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (cb - 1)))
  have hglobal : (global.card : ℝ) ≤ Real.exp ((K + 1) * L) := by
    apply le_trans _ hdel
    exact_mod_cast (show global.card ≤ global.card +
      (Fintype.card (MovingRegularSlot (n + 2) (4 + r) m) + 4 * (n + 2) * 2 ^ (n + 2)) +
      outside.length by omega)
  have hnumer := hnumeric global Qν hglobal hν hνmass arch (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr hgap)
  apply he.trans
  have hexp :
      Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ (n + 2) : ℕ) * (cb - 1))) *
      Real.exp (((2 ^ (n + 2) * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) = arch := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreassoc (a b c d e : ℝ) : (a * b * c) * (d * e) = (a * d) * (b * c) * e := by ring
  rw [hreassoc, hexp]
  simpa only [gain, Nat.cast_pow, Nat.cast_ofNat] using hnumer

end Ostmann

end OAI
