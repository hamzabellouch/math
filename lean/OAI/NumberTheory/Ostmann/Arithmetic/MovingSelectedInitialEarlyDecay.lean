import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedInitialEarlyDiagonal
import OAI.NumberTheory.Ostmann.Construction.EarlyDiagonalBudget

namespace OAI

/-! # The actual first two diagonals satisfy the iteration reserve -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_early_diagonal_decay
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r k : ℕ) (hk : 0 < k) (hn : n < k) (hearly : n ≤ 1)
    (A Wwin Bφ Dφ c K εdiag Bs BD Bz B : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (hBs : 0 ≤ Bs) (hBD0 : 0 ≤ BD) (hBz : 9 ≤ Bz)
    (hmassBudget : 4 * (K + 1) * r ≤ (k : ℝ) ^ 4)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
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
      0 ≤ Δ → Δ ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
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
      (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
        ((2 ^ n * 4 : ℕ) : ℝ) * b -
          ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
        -spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) m) →
      movingAmplitudeDiagonal Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val bsize d rinit cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G n r m (smoothGiantPrimeRange H)
        (Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊)
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H)
        (fun i => primeSubsetPrior primes (Qν i)) (normalizedResidueFamily setsReg) ggiant favorable ≤
      Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * m) := by
  let gain := max 0 ((Real.log 2 + Real.log ((k : ℝ) ^ 4 / (1 / 16000 : ℝ)) +
    Real.log (2 ^ n : ℕ) + 1 + 2 * B + 6) * (2 ^ n : ℕ))
  have hdiag := P.moving_selected_initial_early_log_diagonal C hM ψ n r k hk hn
    A Wwin Bφ Dφ c K εdiag hA hWwin hBφ hDφ hc hK hεdiag hdepth
  have hnumeric := selected_diagonal_budget hM n r k hk c K Bs BD Bz B 1 εdiag
    hc hK hBs hBD0 (by norm_num) hεdiag.le (by simpa only [one_mul] using hmassBudget) hBz hBD
  filter_upwards [hdiag, hnumeric] with L hdiag hnumeric
  intro bsize hsize
  have hdiag := hdiag bsize hsize
  dsimp only at hdiag hnumeric ⊢
  rw [hsize] at hnumeric
  intro tierB primes hprimes _ d rinit sl sr fallback childBound pivotBound V outside p _ Dq sets
    primeLo cutoff tier X Δ hi b φ G global Qμ Qν setsReg cb cd lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hΔupper hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb hφ1 hlower hvr hgap
  have he := hdiag tierB primes hprimes d rinit sl sr fallback childBound pivotBound V outside p Dq sets
    primeLo cutoff tier X Δ hi b
    φ G global Qμ Qν setsReg cb cd lower ggiant favorable
    hlen hV hcard hVn hV0 hΔ hhi hwindow hH hB
    hm hp hsets hsetsp hpupper hφ0 hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp hHbig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg hb hφ1 hlower hvr
  let m := bsize + bsize
  let H := G (n + 1)
  let arch := Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + 1 +
    ((2 ^ n * 4 : ℕ) : ℝ) * b -
      ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)))
  have hglobal : (global.card : ℝ) ≤ Real.exp ((K + 1) * L) := by
    apply le_trans _ hdel
    exact_mod_cast (show global.card ≤ global.card +
      (Fintype.card (MovingRegularSlot n (4 + r) m) + 4 * n * 2 ^ n) +
      outside.length by omega)
  have hnumer := hnumeric global Qν hglobal hν hνmass arch (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr hgap)
  apply he.trans
  have hexp :
      Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H - (H - 1) -
        ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2))) *
      Real.exp (((2 ^ n * 4 : ℕ) : ℝ) * b +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + H) = arch := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hreassoc (a b c d e : ℝ) : (a * b * c) * (d * e) = (a * d) * (b * c) * e := by ring
  rw [hreassoc, hexp]
  have henergy := early_diagonal_energy_le n hearly (m : ℝ)
    (Real.exp ((2 ^ n : ℕ) * Δ +
      (Real.log 12 + 1) * (2 ^ n : ℕ) * m + εdiag * m))
    (Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) (Real.exp (-gain * m))
    (Nat.cast_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _)
  apply (mul_le_mul_of_nonneg_left henergy (by positivity)).trans
  apply le_trans ?_ hnumer
  dsimp only [gain, arch, m, H]
  push_cast
  gcongr
  simpa only [Nat.cast_add] using hΔupper

end Ostmann

end OAI
