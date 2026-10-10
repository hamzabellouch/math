import OAI.NumberTheory.Ostmann.Construction.OriginalTwoTailContradiction
import OAI.NumberTheory.Ostmann.Construction.OriginalLocalScaleBudget
import OAI.NumberTheory.Ostmann.Construction.OriginalEndpointTransfer

namespace OAI

/-! # The original contradiction with its integer parameters constructed

The endpoint scale, moment orders and Fourier cutoff are chosen explicitly.
Only the actual two tails, populated dyadic prime block and small-prime masks
remain as geometric data.
-/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_dyadic_two_tail_contradiction (hBonami : PublishedBonamiBound)
    (P₀ : PublishedProgressionInput) (H : PublishedRealZeroInput P₀)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (C₀ : ℝ) (hMertens : MertensLowerBound C₀)
    (cψ a c C B : ℝ) (hcψ : 0 < cψ) (ha : 0 < a) (hc : 0 < c)
    (hC : 500 ≤ C) (hB : 3 ≤ B) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, B ^ 2 < |x| → 𝓕 ψ x = 0) (hCψ : (𝓕 ψ 0).re ≤ C) :
    ∃ L₀ : ℝ, ∀ᶠ V : ℝ in atTop, ∀ L : ℝ, L₀ ≤ L →
      V ^ (8 / 5 : ℝ) / 2 ≤ L → L ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) →
      ∀ (z : ℕ) (Q P : Finset ℕ), 2 ≤ z → Real.log (z : ℝ) = V →
      (∀ p ∈ Q, p.Prime ∧ 1000000 ≤ p) →
      (∀ p ∈ P, p.Prime ∧ Odd p) →
      (∀ p ∈ P, z ≤ p ∧ p < 2 * z) → (z : ℝ) ≤ C * V * P.card →
      V ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ V ^ (9999999 / 10000000 : ℝ) →
      2 ≤ Q.toList.prod → (Q.toList.prod : ℝ) ≤ Real.exp (V / 50) →
      (∀ p ∈ Q, ∀ q ∈ P, p < q) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (S U : Finset ℤ),
      (∀ x ∈ S, 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ Real.exp L) →
      (∀ y ∈ U, -Real.exp L ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (S.card : ℝ) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (U.card : ℝ) →
      (∀ p ∈ Q, (D p).card / (p : ℝ) ≤ 2 / 3) →
      (∀ n ∈ S, ∀ p ∈ Q, (n : ZMod p) ∈ D p) →
      ∀ (ε δ : ℕ → ℝ) (t : ℕ → ℤ),
      (∀ p ∈ P, ε p = 1 ∨ ε p = -1) → (∀ p ∈ P, δ p = 1 ∨ δ p = -1) →
      (∀ p ∈ P, S.card * c ≤ ∑ n ∈ S, orientedQuadraticValue ε t n p) →
      (∀ p ∈ P, U.card * c ≤ ∑ n ∈ U, orientedQuadraticValue δ t n p) →
      (∀ x ∈ S, ∀ y ∈ U, (x - y).natAbs.Prime ∧
        Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) → False := by
  obtain ⟨η, L₀, _, _, _, hno⟩ := eventual_original_two_tail_contradiction
    hBonami P₀ H hSiegel sieve C₀ hMertens cψ (a / 8) c C B hcψ (by positivity) hc
    hC hB ψ hreal hψ0 hψ1 hsupp hCψ
  refine ⟨L₀, ?_⟩
  filter_upwards [hno, eventual_original_local_scales,
    eventual_originalMomentOrder_population C (by linarith),
    eventually_ge_atTop (max 2 (25 * B ^ 2 / 12))] with V hnoV hlocal hpopulation hV
  intro L hL hLlo hLhi z Q P hz hlog hQ hP hrange hpop hKlo hK3 hKhi hQ2 hQprod
    hsep D S U hS hU hSsize hUsize hD hSD ε δ t hε hδ hSbias hUbias hcross
  have hV2 : 2 ≤ V := (le_max_left _ _).trans hV
  have hVp : 0 < V := by linarith
  obtain ⟨hVL, hLV, h13, hklo, hkhi, hklog, hl, hllo, hlhi⟩ := hlocal L hLlo hLhi
  have hLp : 0 < L := by linarith
  have hBexp : B ^ 2 ≤ Real.exp (12 * V / 25) := by
    have hv := (le_max_right _ _).trans hV
    linarith [Real.add_one_le_exp (12 * V / 25)]
  have hzpos : 0 < z := by omega
  have hpr : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hqr : ∀ p ∈ Q, p.Prime := fun p hp => (hQ p hp).1
  have hrange' : ∀ p ∈ P, z ≤ p ∧ p ≤ 2 * z := fun p hp =>
    ⟨(hrange p hp).1, (hrange p hp).2.le⟩
  have hprod := original_prime_product_scale P z L V hzpos hVp hlog hLp.le hpr hrange' hklog
  have hQpos : (0 : ℝ) < Q.toList.prod := by exact_mod_cast (show 0 < Q.toList.prod by omega)
  have hsqrt : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hsize (W : Finset ℤ) (hW : a * Real.exp (L / 2) / L ^ 3 ≤ (W.card : ℝ)) :
      (a / 8) * Real.sqrt (Real.exp L) / V ^ 6 ≤ (W.card : ℝ) := by
    rw [hsqrt]
    exact (local_tail_size_transfer a L V ha.le hLp hLV).trans hW
  have hZ := doubled_prime_endpoint_le_exp z hzpos
  rw [hlog] at hZ
  have hcardz : (P.card : ℝ) ≤ z := by exact_mod_cast dyadic_block_card_le P z hrange
  have hz2 : (z : ℝ) ≤ (2 * z : ℕ) := by exact_mod_cast (show z ≤ 2 * z by omega)
  have hPcard : (P.card : ℝ) ≤ Real.exp (V + 1) := hcardz.trans (hz2.trans hZ)
  have hexpz : Real.exp V = (z : ℝ) := by
    rw [← hlog, Real.exp_log (by exact_mod_cast hzpos)]
  have hpop' : Real.exp V ≤ C * V * P.card := by rw [hexpz]; exact hpop
  have hmin : ∀ p ∈ P, Real.exp V ≤ (p : ℝ) := by
    intro p hp
    rw [← hlog, Real.exp_log (by exact_mod_cast hzpos)]
    exact_mod_cast (hrange p hp).1
  have hX : Real.exp L ≤ Real.exp (((originalMomentOrder L V - 10 : ℕ) : ℝ) * V) :=
    Real.exp_le_exp.mpr (originalMomentOrder_scale L V hLp.le hVp).2.1
  exact hnoV Q P hqr hpr (fun p hp => (hP p hp).2) D L (Real.exp L) rfl hVL hLV hL
    (Real.one_le_exp hLp.le) (original_tail_weight_cutoff L V B _ hVp h13 hQpos hQprod hBexp)
    S hS (hsize S hSsize) hD hSD ε t hε hSbias
    (originalMomentOrder L V) (originalHolderOrder V) (originalFrequencyCutoff V) (2 * z)
    (originalMomentOrder_scale L V hLp.le hVp).1 (originalMomentOrder_even L V)
    (hpopulation L P.card hLlo hLhi hpop')
    hklo hkhi hKlo hK3 hKhi (fun p hp => (hQ p hp).2) hQprod hQ2
    hpop'
    hPcard hX (separated_prime_products_coprime Q P hqr hpr hsep _)
    (fun p hp => (hrange p hp).2.le) hmin (by omega) hZ
    (original_upper_endpoint_power z L V hzpos hVp hlog hLp.le hklog h13)
    hl hllo hlhi (originalFrequencyCutoff_bounds V hV2).1 (originalFrequencyCutoff_bounds V hV2).2
    (fun M hM => ⟨originalFrequencyCutoff_covers V B _ _ (by positivity) (by positivity)
      (hprod M hM).2 hQprod hBexp, (hprod M hM).1,
      (hprod M hM).2.trans (Real.exp_le_exp.mpr (by linarith))⟩)
    U hU (hsize U hUsize) δ hδ hUbias hcross

end Ostmann

end OAI
