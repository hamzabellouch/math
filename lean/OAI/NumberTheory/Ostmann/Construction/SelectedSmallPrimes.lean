import OAI.NumberTheory.Ostmann.Construction.SmallPrimeSupply

namespace OAI

/-! # Selecting the actual small-prime amplification data -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_selected_small_primes (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ L₀ : ℝ, ∀ᶠ T : ℝ in atTop, ∀ L : ℝ,
      L₀ ≤ L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L → ∀ V : ℝ, T / 2 ≤ V → V ≤ 2 * T →
      ∃ Q : Finset ℕ,
        (∀ p ∈ Q, p.Prime ∧ 1000000 ≤ p ∧ Real.log (p : ℝ) ≤ 2 * T ^ (1 / 10000000 : ℝ)) ∧
        3000 ≤ Q.card ∧ V ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) ∧
        (Q.card : ℝ) ≤ V ^ (9999999 / 10000000 : ℝ) ∧
        2 ≤ Q.toList.prod ∧ (Q.toList.prod : ℝ) ≤ Real.exp (V / 50) ∧
        (∀ p ∈ Q, (tailDensityMask A N p).card / (p : ℝ) ≤ 2 / 3) ∧
        (∀ n ∈ positiveSummandTail A (summandTailCutoff L) hi,
          ∀ p ∈ Q, (n : ZMod p) ∈ tailDensityMask A N p) := by
  obtain ⟨N, L₀, hblocks⟩ := exists_eventual_density_prime_block hsize hA hB h C hM
  let D := 8 + 8 / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : ∀ᶠ V : ℝ in atTop,
      (∀ (z : ℕ) (P : Finset ℕ), 0 < z →
        V ^ (1 / 10000000 : ℝ) / 2 ≤ Real.log (2 * (z : ℝ)) →
        Real.log (2 * (z : ℝ)) ≤ 8 * V ^ (1 / 10000000 : ℝ) →
        (z : ℝ) ≤ D * Real.log z * P.card → amplificationPrimeCount V z ≤ P.card) ∧
      3000000 ≤ V ^ (9999999 / 10000000 : ℝ) ∧ 0 < V := by
    filter_upwards [eventual_amplification_prime_count_available D hD,
      (tendsto_rpow_atTop (show (0 : ℝ) < 9999999 / 10000000 by norm_num)).eventually_ge_atTop 3000000,
      eventually_gt_atTop (0 : ℝ)] with V hs hp hV
    exact ⟨hs, hp, hV⟩
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp hnum
  refine ⟨N, L₀, ?_⟩
  filter_upwards [hblocks,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10000000 by norm_num)).eventually_ge_atTop
      (max 1000000 (Real.log 2)), eventually_ge_atTop (max 4096 (2 * V₀))]
    with T hblock hU hT
  intro L hL hTL hLU hi hhi V hVlo hVhi
  have hTbig : 4096 ≤ T := (le_max_left _ _).trans hT
  have hTp : 0 < T := by linarith
  have hVlarge : V₀ ≤ V := by have := (le_max_right _ _).trans hT; linarith
  obtain ⟨hsupply, hpower, hVp⟩ := hV₀ V hVlarge
  obtain ⟨hNlo, z, P, hz, hPne, hPband, hrange, hpop, hbal⟩ := hblock L hL hTL hLU hi hhi
  have hlogs := primeBlock_log_bounds P z (T ^ (1 / 10000000 : ℝ)) hz hPne hPband hrange
  have hlogbounds := small_primeBlock_log_bounds T V z hTp hVlo hVhi
    ((le_max_right _ _).trans hU) (by omega) hlogs.1 hlogs.2
  have hcounts := amplificationPrimeCount_bounds V z hVp hlogbounds.1 hlogbounds.2 hpower
  have hcount := hsupply z P (by omega) hlogbounds.1 hlogbounds.2 hpop
  obtain ⟨Q, hQP, hcard, hQprime, hprod2, hprod⟩ := exists_amplification_prime_subset P z V hz hVp.le
    (fun p hp => (logPrimeBand_mem (hPband hp)).1) (fun p hp => (hrange p hp).2) hcount (by omega)
  have hQband : Q ⊆ logPrimeBand (T ^ (1 / 10000000 : ℝ)) := hQP.trans hPband
  have hUT : T ^ (1 / 10000000 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (show (1 / 10000000 : ℝ) ≤ 1 by norm_num)
  have hQcut : Q ⊆ Nat.primesLE (tailCollisionCutoff L) := hQband.trans
    (logPrimeBand_subset_tailCollisionCutoff T L _ hTbig hTL hLU hUT)
  refine ⟨Q, ?_, by omega, ?_, ?_, hprod2, hprod, ?_, ?_⟩
  · intro p hp
    have hb := logPrimeBand_mem (hQband hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hb.1.pos
    have he := (Real.lt_log_iff_exp_lt hp0).mp hb.2.1
    have hm : (1000000 : ℝ) ≤ p := by
      have hu := (le_max_left _ _).trans hU
      linarith [Real.add_one_le_exp (T ^ (1 / 10000000 : ℝ))]
    exact ⟨hQprime p hp, by exact_mod_cast hm, hb.2.2⟩
  · simpa only [hcard] using hcounts.2.1
  · simpa only [hcard] using hcounts.2.2
  · intro p hp
    exact tailDensityMask_density A N p (hQprime p hp).pos (hbal p (hQP hp)).2
  · intro n hn p hp
    apply positiveSummandTail_mem_mask A N (summandTailCutoff L) hi p (hQprime p hp).pos _ hn
    exact (Nat.add_le_add_left (Nat.le_of_mem_primesLE (hQcut hp)) N).trans hNlo

end Ostmann

end OAI
