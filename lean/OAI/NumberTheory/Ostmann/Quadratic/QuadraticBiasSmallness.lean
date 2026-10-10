import OAI.NumberTheory.Ostmann.Construction.DyadicTwoTailContradiction
import OAI.NumberTheory.Ostmann.Construction.SelectedSmallPrimes
import OAI.NumberTheory.Ostmann.Construction.EndpointBaseScale

namespace OAI

/-! # Uniform smallness of translated quadratic biases

The residue partition is fixed before the error tolerance. The proof constructs
both prime blocks, all integer parameters and the positive and reflected tails.
-/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem eventual_small_prime_separation :
    ∀ᶠ T : ℝ in atTop, 2 * T ^ (1 / 10000000 : ℝ) < T := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 9999999 / 10000000 by norm_num)).eventually_ge_atTop 4,
    eventually_gt_atTop (0 : ℝ)] with T hpow hT
  have he : T ^ (1 / 10000000 : ℝ) * T ^ (9999999 / 10000000 : ℝ) = T := by
    rw [← Real.rpow_add hT]; norm_num
  have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hT.le (1 / 10000000 : ℝ))
  rw [he] at hh
  nlinarith [Real.rpow_pos_of_pos hT (1 / 10000000 : ℝ)]

theorem eventual_translated_quadratic_bias_lt
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C₀ : ℝ) (hM : MertensEstimate C₀)
    (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℕ → ℤ,
      (∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) *
        |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) < δ * T := by
  obtain ⟨a, Cpop, Lbig, ha, hCpop, hblocks⟩ :=
    exists_eventual_biased_prime_block hsize hA hB h N hN C₀ hM δ hδ hδU
  let C := max Cpop (𝓕 ψ 0).re
  have hC : 500 ≤ C := hCpop.trans (le_max_left _ _)
  obtain ⟨Lno, hno⟩ := eventual_dyadic_two_tail_contradiction hBonami P₀ H hSiegel sieve
    C₀ hM.lower cψ a (δ / 16) C Bψ hcψ ha (by positivity) hC hBψ ψ hreal hψ0 hψ1 hsupp
    (le_max_right _ _)
  obtain ⟨Vno, hVno⟩ := eventually_atTop.mp hno
  obtain ⟨Nsmall, Lsmall, hsmall⟩ := exists_selected_small_primes hsize hA hB h C₀ hM
  obtain ⟨_, _, htails⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨Ltails, hLtails⟩ := eventually_atTop.mp htails
  filter_upwards [hblocks, hsmall, eventual_endpoint_scale, eventual_small_prime_separation,
    eventually_ge_atTop (max 2 (max Lbig (max Lsmall (max Lno (max Ltails (2 * Vno))))))]
    with T hblock hsm hend hsep hT t
  by_contra hnot
  have hbias := le_of_not_gt hnot
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hmax : max Lbig (max Lsmall (max Lno (max Ltails (2 * Vno)))) ≤ T :=
    (le_max_right _ _).trans hT
  obtain ⟨hX1, hXL, hTL, hT32, hL2, hsc⟩ := hend
  let L := endpointLogScale T
  let X := endpointSize T
  have hXL' : (X : ℝ) = Real.exp L := hXL.symm
  have hLbig : Lbig ≤ L := (le_max_left _ _).trans (hmax.trans hTL)
  have hsmallmax : max Lsmall (max Lno (max Ltails (2 * Vno))) ≤ T :=
    (le_max_right _ _).trans hmax
  have hLsmall : Lsmall ≤ L := (le_max_left _ _).trans (hsmallmax.trans hTL)
  have hnomax : max Lno (max Ltails (2 * Vno)) ≤ T := (le_max_right _ _).trans hsmallmax
  have hLno : Lno ≤ L := (le_max_left _ _).trans (hnomax.trans hTL)
  have htailmax : max Ltails (2 * Vno) ≤ T := (le_max_right _ _).trans hnomax
  have hLtail : Ltails ≤ L := (le_max_left _ _).trans (htailmax.trans hTL)
  have hVcut : 2 * Vno ≤ T := (le_max_right _ _).trans htailmax
  obtain ⟨z, P, ε, hz, hPne, hPband, hrange, hpop, hsa, hsb, hpoint⟩ :=
    hblock L hLbig hL2 hT32 X hXL' t hbias
  have hlogs := primeBlock_log_bounds P z T hz hPne hPband hrange
  let V := Real.log (z : ℝ)
  obtain ⟨hTV, hVp, hLVlo, hLVhi⟩ := hsc V hlogs.1.le hlogs.2
  have hVlarge : Vno ≤ V := by linarith
  obtain ⟨Q, hQ, hK3, hKlo, hKhi, hQ2, hQprod, hD, hSD⟩ :=
    hsm L hLsmall hT32 hL2 X hXL' V hTV hlogs.2
  have hprime : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    have hh := logPrimeBand_mem (hPband hp)
    refine ⟨hh.1, hh.1.odd_of_ne_two ?_⟩
    intro he
    rw [he] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    linarith [hh.2.1]
  have hsepQP : ∀ p ∈ Q, ∀ q ∈ P, p < q := by
    intro p hp q hq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).1.pos
    have hlogsPQ : Real.log (p : ℝ) < Real.log (q : ℝ) :=
      (hQ p hp).2.2.trans_lt (hsep.trans (logPrimeBand_mem (hPband hq)).2.1)
    exact_mod_cast (Real.log_lt_log_iff hp0 (by exact_mod_cast (hprime q hq).1.pos)).mp hlogsPQ
  have hpopC : (z : ℝ) ≤ C * V * P.card := by
    apply hpop.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hVp.le) (Nat.cast_nonneg _)
  obtain ⟨_, _, hSbounds, hUbounds, hcross⟩ := hLtails L hLtail X hXL'
  have hSbounds' : ∀ x ∈ positiveSummandTail A (summandTailCutoff L) X,
      0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ Real.exp L := by simpa only [hXL'] using hSbounds
  have hUbounds' : ∀ y ∈ negativeSummandTail B (summandTailCutoff L) X,
      -Real.exp L ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0 := by simpa only [hXL'] using hUbounds
  exact hVno V hVlarge L hLno hLVlo hLVhi z Q P hz rfl
    (fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.1⟩) hprime hrange hpopC hKlo hK3 hKhi hQ2 hQprod
    hsepQP (tailDensityMask A Nsmall) (positiveSummandTail A (summandTailCutoff L) X)
    (negativeSummandTail B (summandTailCutoff L) X) hSbounds' hUbounds' hsa hsb hD hSD
    ε (fun p => -ε p) t (fun p hp => (hpoint p hp).1)
    (fun p hp => by rcases (hpoint p hp).1 with hh | hh <;> simp [hh])
    (fun p hp => (hpoint p hp).2.2.2.1) (fun p hp => (hpoint p hp).2.2.2.2) hcross

end Ostmann

end OAI
