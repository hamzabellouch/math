import OAI.NumberTheory.Ostmann.QuadraticCenter.SplitPrimeAfterExclusion
import OAI.NumberTheory.Ostmann.QuadraticSieve.SmallKernelCharacters

namespace OAI

/-! # The retained split-prime estimate for every nonzero squarefree kernel -/

namespace Ostmann

open scoped BigOperators Classical

/-- This includes the principal kernel 1 and all three small nonprincipal
kernels. The constants and exclusion set are uniform over every kernel. -/
theorem all_kernel_split_prime_mass (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K C : ℝ, 0 < A ∧ 0 < K ∧ 0 < C ∧
      ∀ (d : ℤ) (Q₀ Q D Y : ℕ) (R s : ℝ),
        Squarefree d.natAbs → d ≠ 0 →
        2 ≤ Q₀ → 4 * d.natAbs ≤ Q₀ → 0 < Q → 0 < D → 0 < Y →
        d.natAbs ∣ D → 0 ≤ R →
        2 * (A + H.errorConstant) ≤ Real.log (4 * (Q₀ : ℝ)) →
        1 < s → s ≤ 2 → s ≤ 1 + 1 / Real.log (4 * (Q₀ : ℝ)) →
        d ∉ pageKernelExclusion P Q₀ R →
        splitPrimeMassLower P H A K C ε Q₀ Q D Y R s ≤
          ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
            Real.log p / (p : ℝ) := by
  obtain ⟨A, K, hA, hK, hchar⟩ := retained_character_prime_lower P H hSiegel ε hε
  obtain ⟨Cu, hCu, hmass⟩ := exists_unsignedPrimeMass_error
  obtain ⟨Ct, hCt, htail⟩ := exists_unsignedPrimeTail_bound
  obtain ⟨Ce, hCe, hcharsum⟩ := exists_realPrimeSeries_error
  let C := Cu + Ct
  have hCuC : Cu ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨A, K, C, hA, hK, by dsimp [C]; positivity, ?_⟩
  intro d Q₀ Q D Y R s hsf hd hQ₀ hdQ₀ hQ hD hY hdD hR hsize hs hs2 hss hout
  obtain ⟨hu, hU⟩ := hmass s hs hs2
  obtain ⟨ht, hT⟩ := htail Q s hQ hs hs2
  let B := 2 * zeroComparisonConstant P * Real.log (4 * (Q₀ : ℝ)) +
    K * R ^ ε + H.errorConstant + A + 2
  have hJ : Summable (jacobiPrimeTerm d s) ∧ -B ≤ ∑' n, jacobiPrimeTerm d s n := by
    by_cases hone : d = 1
    · have heq : jacobiPrimeTerm d s = unsignedPrimeTerm s := by
        subst d
        funext n
        simp only [jacobiPrimeTerm, unsignedPrimeTerm, jacobiSym.one_left, Int.cast_one, one_mul]
      rw [heq]
      have hlog : 0 ≤ Real.log (4 * (Q₀ : ℝ)) := by
        apply Real.log_nonneg
        have hQr : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
        linarith
      have hCz : 0 ≤ zeroComparisonConstant P := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 5) (le_max_left _ _)
      have hHC := H.errorConstant_nonneg
      have hB : 0 ≤ B := by dsimp [B]; positivity
      exact ⟨hu, le_trans (neg_nonpos.mpr hB) (tsum_nonneg (unsignedPrimeTerm_nonneg s))⟩
    · obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, _, hv⟩ :=
        exists_nonprincipal_kernel_character d hsf hd hone
      have hret := page_kernel_retention P Q₀ R d χ N hN hNq hqN hdN hqd hout
      have hb := hchar χ Q₀ R s hQ₀ (hqd.trans hdQ₀) hR hsize hs hss hret
      let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
      have hc := jacobiPrimeSeries_comparison d χ s (by linarith) hv
        (hcharsum χ.modulus χ.character s hs).1
      refine ⟨hc.1, ?_⟩
      have hdiff := (abs_le.mp hc.2).1
      dsimp [B]
      linarith
  have hUl : 1 / (s - 1) - C ≤ ∑' n, unsignedPrimeTerm s n := by
    have hh := (abs_le.mp hU).1
    linarith
  have hTl : (∑' n, unsignedPrimeTail Q s n) ≤
      (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) :=
    hT.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg Q) _))
  have hsplit := retained_split_mass_from_series d D Q Y s _ B _ hdD hD hY hs.le
    hu hJ.1 ht hUl hJ.2 hTl
  change splitPrimeMassLower P H A K C ε Q₀ Q D Y R s ≤ _
  apply hsplit.trans
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) hp0
    (Real.self_le_rpow_of_one_le hp1 hs.le)

end Ostmann

end OAI
