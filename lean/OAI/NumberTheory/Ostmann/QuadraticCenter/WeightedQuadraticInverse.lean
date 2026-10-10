import OAI.NumberTheory.Ostmann.QuadraticCenter.EffectiveQuadraticInverse
import OAI.NumberTheory.Ostmann.Characters.WeightedPhaseExtraction

namespace OAI

/-! # The inverse phase conclusion for the actual weighted quadratic sum -/

namespace Ostmann

open scoped BigOperators

/-- Finite variation removes the smooth weight. The resulting explicit losses
are harmless exponential factors when δ=exp(-K), as in the manuscript. -/
theorem weighted_quadratic_inverse (w : ℕ → ℂ) (α β δ : ℝ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N)
    (hlarge : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j * realQuadraticPhase α β j‖) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / δ ^ 2 ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨n, hn, hnN, hsum⟩ := exists_large_prefix_of_weighted_sum w
    (realQuadraticPhase α β) N (δ * N) (by positivity) hlarge
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hnorm : ‖∑ j ∈ Finset.range n, realQuadraticPhase α β j‖ ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, ‖realQuadraticPhase α β j‖ := norm_sum_le _ _
      _ = n := by simp [realQuadraticPhase]
  have hδN : δ * N ≤ (n : ℝ) := (hsum.trans_le hnorm).le
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hnp hnNR
  have hnscale : 512 * (1 + 2 * Real.log (n : ℝ)) ≤ δ ^ 2 * n := by
    have hh := mul_le_mul_of_nonneg_left hδN (sq_nonneg δ)
    nlinarith
  have hlarge' : δ ^ 2 * (n : ℝ) ^ 2 ≤ ‖∑ j ∈ Finset.range n, realQuadraticPhase α β j‖ ^ 2 := by
    have hh : δ * (n : ℝ) ≤ ‖∑ j ∈ Finset.range n, realQuadraticPhase α β j‖ := by
      have ht := mul_le_mul_of_nonneg_left hnNR hδ.le
      linarith
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ δ * (n : ℝ)) hh 2
    nlinarith
  obtain ⟨q, hq, hqsize, hqapprox⟩ := effective_quadratic_inverse α β (δ ^ 2) n hn
    (sq_pos_of_pos hδ) (by nlinarith) hnscale hlarge'
  refine ⟨q, hq, hqsize, hqapprox.trans ?_⟩
  have hden : δ ^ 4 * (N : ℝ) ^ 2 ≤ δ ^ 2 * (n : ℝ) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ δ * (N : ℝ)) hδN 2
    have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg δ)
    nlinarith
  have hB : 0 ≤ 1024 * (1 + 2 * Real.log (N : ℝ)) := by
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  calc
    _ ≤ 1024 * (1 + 2 * Real.log (N : ℝ)) / (δ ^ 2 * (n : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hB (by positivity) hden

end Ostmann

end OAI
