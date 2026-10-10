import OAI.NumberTheory.Ostmann.Construction.OriginalTailCenter
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterPopulationContradiction
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterEndpointBounds

namespace OAI

/-! # Original biased tails lead to a contradiction

The Fourier and inverse-phase step produces the center used by the actual
large-sieve and population argument. Only the cited published inputs remain.
-/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_original_two_tail_contradiction (hBonami : PublishedBonamiBound)
    (P₀ : PublishedProgressionInput) (H : PublishedRealZeroInput P₀)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (C₀ : ℝ) (hMertens : MertensLowerBound C₀)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
    ∀ᶠ T : ℝ in atTop, ∀ (Q P : Finset ℕ) (_hQ : ∀ p ∈ Q, p.Prime),
      ∀ _hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Odd p) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (L X : ℝ),
      X = Real.exp L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 → L₀ ≤ L →
      1 ≤ X → B ^ 2 < X / Q.toList.prod →
      ∀ (S : Finset ℤ), (∀ n ∈ S, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) →
      a * Real.sqrt X / T ^ 6 ≤ (S.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε : ℕ → ℝ) (t : ℕ → ℤ), (∀ p ∈ P, ε p = 1 ∨ ε p = -1) →
      (∀ p ∈ P, (S.card : ℝ) * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      ∀ k l N Z : ℕ, 10 ≤ k → Even k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      2 ≤ Q.toList.prod →
      Real.exp T ≤ C * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      X ≤ Real.exp (((k - 10 : ℕ) : ℝ) * T) →
      (∀ M ∈ primeSubsetProducts P k, Q.toList.prod.Coprime M) →
      (∀ p ∈ P, p ≤ Z) → (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → (Z : ℝ) ≤ Real.exp (T + 1) → (Z : ℝ) ^ k ≤ Real.exp (2 * L) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      (∀ M ∈ primeSubsetProducts P k,
        B ^ 2 * ((M : ℝ) / X) * Q.toList.prod ≤ N ∧
        Real.exp (10 * T) ≤ (M : ℝ) / X ∧ (M : ℝ) / X ≤ Real.exp (14 * T)) →
      ∀ (U : Finset ℤ), (∀ n ∈ U, -X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 0) →
      a * Real.sqrt X / T ^ 6 ≤ (U.card : ℝ) →
      ∀ δ : ℕ → ℝ, (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
      (∀ p ∈ P, (U.card : ℝ) * c ≤ ∑ n ∈ U, orientedQuadraticValue δ t n p) →
      (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
        Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) → False := by
  obtain ⟨η, L₀, hη, hηU, hL₀, hno⟩ := common_center_biased_populations_impossible
    P₀ H hSiegel sieve C hC C₀ hMertens a c ha hc
  refine ⟨η, L₀, hη, hηU, hL₀, ?_⟩
  filter_upwards [hno, eventual_original_tail_commonCenter hBonami cψ a c C B hcψ ha hc
    hC hB ψ hreal hψ0 hψ1 hsupp hCψ, eventual_commonCenter_denominator η hη,
    eventually_ge_atTop (3 : ℝ)] with T hnoT hcenter hdenom hT
  intro Q P hQ hP hodd D L X hXeq hTL hLU hL hX hBX S hS hsize hD hSD ε t hε hbias
    k l N Z hk heven hksize hkL hkU hK hK3 hKU hlarge hQprod hQ2 hpop hPU hXU
    hcop hPZ hmin hZ hZU hZL hl hlL hlU hN1 hN hscale U hU hUsize δ hδ hUbias hcross
  obtain ⟨b, hb, n, hn, h, m, hm, hmcut, hred, hhn, hbig, hrel, ht⟩ := hcenter Q P hQ hP
    hodd D X hX hBX S hS hsize hD hSD ε t hε hbias k l N Z hk heven hksize hkL hkU
    hK hK3 hKU hlarge hQprod hQ2 hpop hPU hXU hcop hPZ hmin hZ hZU hl hlL hlU hN1 hN hscale
  let R := matchingPrimes P b t n
  have hRP : R ⊆ P := Finset.filter_subset _ _
  have hRprime : ∀ p ∈ R, p.Prime := fun p hp => hP p (hRP hp)
  have hRpos : 0 < R.card := by exact_mod_cast (Real.exp_pos _).trans_le hbig
  have hPpos : 0 < (P.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hRpos (Finset.card_le_card hRP))
  have hmprime : ∀ p ∈ R, m < p := by
    intro p hp
    apply lt_of_le_of_lt hmcut
    exact commonCenter_denominator_lt_primes T ⌈Real.exp (13 * T / 100)⌉₊ p hT
      (commonCenter_original_cutoffs T X k (by linarith) hX hXU).2.1 (hmin p (hRP hp))
  have hnabs : |n| ≤ (⌈X * Real.exp (13 * T / 100)⌉₊ : ℕ) := by
    have hn' := Finset.mem_Ico.mp hn
    apply abs_le.mpr
    constructor <;> omega
  have hhabs : |h| ≤ (⌈X * Real.exp (13 * T / 100)⌉₊ : ℕ) := hhn.trans hnabs
  have hexpZ : Real.exp T ≤ (Z : ℝ) := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hRpos
    exact (hmin p (hRP hp)).trans (by exact_mod_cast hPZ p (hRP hp))
  have hLgeT : T ≤ L := by
    have hp : T ≤ T ^ (3 / 2 : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ T by linarith)
        (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    exact hp.trans hTL
  have hLpos : 0 < L := by linarith
  have hsqrt : Real.sqrt X = Real.exp (L / 2) := by
    rw [hXeq]
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hsizeTransfer : a * Real.exp (L / 2) / L ^ 6 ≤ a * Real.sqrt X / T ^ 6 := by
    rw [hsqrt]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by linarith) hLgeT 6)
  apply hnoT L P.card R k Z (Z ^ k) m h ε δ t S U hTL hLU hL (by omega) hkU
    hPpos hpop hrel hbig hZU hZ (one_le_pow₀ hZ) le_rfl hZL hRprime
    (fun p hp => hodd p (hRP hp)) (fun p hp => hPZ p (hRP hp))
    (fun p hp => hε p (hRP hp)) (fun p hp => hδ p (hRP hp))
    (fun p hp => (Real.le_log_iff_exp_le (by exact_mod_cast (hRprime p hp).pos)).mpr (hmin p (hRP hp)))
    hmprime ht hm ((by exact_mod_cast hmcut : (m : ℝ) ≤ ⌈Real.exp (13 * T / 100)⌉₊).trans (hdenom L hTL)) hred
    _ _ (fun p hp => hbias p (hRP hp)) (fun p hp => hUbias p (hRP hp))
    _ _ _ (hsizeTransfer.trans hsize) (hsizeTransfer.trans hUsize)
  · intro x hx
    apply commonCenter_endpoint_power_bound T X k Z m h x hT hX hk hXU hmcut hhabs
    · rw [abs_of_nonneg (hS x hx).1]; exact (hS x hx).2
    · exact hexpZ
  · intro x hx
    apply commonCenter_endpoint_power_bound T X k Z m h x hT hX hk hXU hmcut hhabs
    · rw [abs_of_nonpos (hU x hx).2]; linarith [(hU x hx).1]
    · exact hexpZ
  · intro x hx y hy
    rw [Int.cast_sub, hXeq] at *
    apply abs_le.mpr
    constructor <;> linarith [(hS x hx).1, (hS x hx).2, (hS y hy).1, (hS y hy).2]
  · intro x hx y hy
    rw [Int.cast_sub, hXeq] at *
    apply abs_le.mpr
    constructor <;> linarith [(hU x hx).1, (hU x hx).2, (hU y hy).1, (hU y hy).2]
  · intro x hx y hy
    refine ⟨(hcross x hx y hy).1, ?_⟩
    have hcut : (kernelSplitCutoff η L : ℝ) ≤ Real.exp (9 * L / 10) := by
      apply (Nat.floor_le (Real.exp_nonneg _)).trans
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hη.le hLpos.le]
    exact_mod_cast hcut.trans_lt (hcross x hx y hy).2

end Ostmann

end OAI
