import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPrimeBlock

namespace OAI

/-! # The actual small-prime block at the manuscript's scale -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_eventual_density_prime_block (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ L₀ : ℝ, ∀ᶠ T : ℝ in atTop, ∀ L : ℝ,
      L₀ ≤ L → T ^ (3 / 2 : ℝ) ≤ L → L ≤ 2 * T ^ 2 →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      N + tailCollisionCutoff L ≤ summandTailCutoff L ∧
      ∃ (z : ℕ) (P : Finset ℕ), 2 ≤ z ∧ P.Nonempty ∧
        P ⊆ logPrimeBand (T ^ (1 / 10000000 : ℝ)) ∧
        (∀ p ∈ P, z ≤ p ∧ p < 2 * z) ∧
        (z : ℝ) ≤ (8 + 8 / Real.log 2) * Real.log z * P.card ∧
        (∀ p ∈ P, (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hlarge⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hlarge
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff N)
  refine ⟨N, max L₁ L₂, ?_⟩
  have hγ : (0 : ℝ) < 1 / 10000000 := by norm_num
  filter_upwards [eventual_tailDefectBudget_negligible a C 1 (1 / 4) (1 / 10000000)
      (by norm_num) (by norm_num) hγ,
    (tendsto_rpow_atTop hγ).eventually_ge_atTop (max 1 (4 * (Real.log 2 + 2 * C))),
    eventually_ge_atTop (4096 : ℝ)] with T hloss hU hT
  intro L hL hTL hLU hi hhi
  have hcut := hL₂ L ((le_max_right _ _).trans hL)
  refine ⟨hcut.2.2, ?_⟩
  let U := T ^ (1 / 10000000 : ℝ)
  have hU1 : 1 ≤ U := (le_max_left _ _).trans hU
  have hUC : 4 * (Real.log 2 + 2 * C) ≤ U := (le_max_right _ _).trans hU
  have hUT : U ≤ T := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (show (1 / 10000000 : ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using hh
  have hband := logPrimeBand_subset_tailCollisionCutoff T L U hT hTL hLU hUT
  obtain ⟨hsa, hsb, _, _, _⟩ := hL₁ L ((le_max_left _ _).trans hL) hi hhi
  have hsa' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A (summandTailCutoff L) hi).card := by
    simpa only [positiveSummandTail_card] using hsa
  have hsb' : a * Real.exp (L / 2) / L ^ 3 ≤ (summandTail B (summandTailCutoff L) hi).card := by
    simpa only [negativeSummandTail_card] using hsb
  have hfull := uniform_tail_collision_bound hA hB N (summandTailCutoff L) hi a L C
    ha hcut.1 hcut.2.1 hhi hcut.2.2
    (fun p hp => hN p (Nat.prime_of_mem_primesLE hp)) hsa' hsb' hM.lower
  apply exists_density_prime_block hA hB N (summandTailCutoff L) hi U C (tailDefectBudget a C L)
    hU1 hUC hM (fun p hp => hN p (logPrimeBand_mem hp).1)
  · apply le_trans _ hfull
    apply Finset.sum_le_sum_of_subset_of_nonneg hband
    intro p hp _
    apply mul_nonneg (Real.log_natCast_nonneg p)
    apply collisionDefect_nonneg
    · exact tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos
    · exact tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
        (hN p (Nat.prime_of_mem_primesLE hp))
    · exact (tailSupport_card_add_complement A N p).le
  · have hh := hloss L hcut.1 hLU
    simpa only [one_pow, div_one, one_div_mul_eq_div] using hh

end Ostmann

end OAI
