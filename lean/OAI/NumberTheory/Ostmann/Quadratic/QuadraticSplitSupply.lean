import OAI.NumberTheory.Ostmann.Quadratic.KernelPrimeCutoffs

namespace OAI

/-! # Uniform split-prime supply outside the explicit exceptional family -/

namespace Ostmann

open scoped BigOperators Classical

/-- All analytic error conditions are discharged by fixed constants and
explicit integer cutoffs. Here L=log X, and the Page threshold is L^100. -/
theorem quadratic_split_supply (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound) :
    ∃ η L₀ : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ (d : ℤ) (D : ℕ),
        Squarefree d.natAbs → d ≠ 0 →
        (d.natAbs : ℝ) ≤ Real.exp (2 * η * L) →
        0 < D → d.natAbs ∣ D → Real.log D ≤ L →
        d ∉ pageKernelExclusion P (kernelConductorCutoff η L) (L ^ (100 : ℕ)) →
        (3 / 100 : ℝ) * L ≤
          ∑ p ∈ (Nat.primesLE (kernelSplitCutoff η L)).filter
            (fun p => ¬p ∣ D ∧ jacobiSym d p = 1), Real.log p / (p : ℝ) := by
  obtain ⟨A, K, C, hA, hK, hC, hmass⟩ :=
    all_kernel_split_prime_mass P H hSiegel (1 / 200) (by norm_num)
  let Cz := zeroComparisonConstant P
  have hCz5 : 5 ≤ Cz := le_max_left _ _
  have hCz : 0 ≤ Cz := by linarith
  obtain ⟨η, hη, hηsmall, hηeq⟩ := exists_kernel_size_exponent Cz hCz5
  let B₀ := 2 * Cz * Real.log 20 + H.errorConstant + A + 2
  let L₀ := max 100 (max (10000 * C) (max ((40000 * K) ^ 2)
    (max (40000 * B₀) (max ((40000 : ℝ) ^ 2)
      (max ((A + H.errorConstant) / η) (20 * Real.log 20))))))
  have hL₀ : 0 < L₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100) (le_max_left _ _)
  refine ⟨η, L₀, hη, hηsmall, hL₀, ?_⟩
  intro L hL d D hsf hd hdsize hD hdD hlogD hout
  have hb : 100 ≤ L ∧ 10000 * C ≤ L ∧ (40000 * K) ^ 2 ≤ L ∧
      40000 * B₀ ≤ L ∧ (40000 : ℝ) ^ 2 ≤ L ∧
      (A + H.errorConstant) / η ≤ L ∧ 20 * Real.log 20 ≤ L := by
    simpa only [L₀, max_le_iff] using hL
  obtain ⟨h100, hCs, hKs, hBs, hLs, hAs, hlogs⟩ := hb
  have hLpos : 0 < L := by linarith
  have hc := kernelConductorCutoff_bounds η L hη.le hLpos.le
  have hq := kernelSplitCutoff_bounds η L hηsmall h100
  have hy := kernelDivisorCutoff_bounds L hLpos
  have hcover := kernelConductorCutoff_covers η L d hdsize
  have hlogpos : 0 < Real.log (4 * (kernelConductorCutoff η L : ℝ)) :=
    lt_of_lt_of_le (by positivity : 0 < 2 * η * L) hc.2.1
  have hsize : 2 * (A + H.errorConstant) ≤
      Real.log (4 * (kernelConductorCutoff η L : ℝ)) := by
    have ha' := (div_le_iff₀ hη).mp hAs
    nlinarith [hc.2.1]
  have hlogupper : Real.log (4 * (kernelConductorCutoff η L : ℝ)) ≤ L / 10 := by
    have heta := mul_le_mul_of_nonneg_right hηsmall hLpos.le
    linarith [hc.2.2]
  have hss : 1 + 10 / L ≤ 1 + 1 / Real.log (4 * (kernelConductorCutoff η L : ℝ)) := by
    have hh : 10 / L ≤ 1 / Real.log (4 * (kernelConductorCutoff η L : ℝ)) :=
      (div_le_div_iff₀ hLpos hlogpos).mpr (by linarith)
    linarith
  have hs : 1 < 1 + 10 / L := by
    have hh : 0 < 10 / L := by positivity
    linarith
  have hs2 : 1 + 10 / L ≤ 2 := by
    have hh : 10 / L ≤ (1 : ℝ) := (div_le_one hLpos).mpr (by linarith)
    linarith
  have hbase := hmass d (kernelConductorCutoff η L) (kernelSplitCutoff η L) D
    (kernelDivisorCutoff L) (L ^ (100 : ℕ)) (1 + 10 / L)
    hsf hd hc.1 hcover hq.1 hD hy.1 hdD (by positivity) hsize hs hs2 hss hout
  have hCsmall : C ≤ L / 10000 := by linarith
  have hBsmall : 2 * Cz * Real.log (4 * (kernelConductorCutoff η L : ℝ)) +
      K * (L ^ (100 : ℕ)) ^ (1 / 200 : ℝ) + H.errorConstant + A + 2 ≤ L / 10000 := by
    rw [page_threshold_siegel_power L hLpos.le]
    apply kernel_zero_error_absorption Cz η K A H.errorConstant L _ hCz hK.le hLpos.le
      hηeq.le hc.2.2 hKs
    exact hBs
  have hEsmall : (kernelDivisorCutoff L : ℝ) + Real.log D / kernelDivisorCutoff L ≤ L / 10000 :=
    kernel_divisor_error_absorption D (kernelDivisorCutoff L) L hLpos hLs hy.2.1 hy.2.2 hlogD
  exact split_prime_mass_of_small_errors d D (kernelSplitCutoff η L) (kernelDivisorCutoff L)
    L C _ hLpos hq.1 hC.le hCsmall hBsmall hEsmall hq.2 hbase

end Ostmann

end OAI
