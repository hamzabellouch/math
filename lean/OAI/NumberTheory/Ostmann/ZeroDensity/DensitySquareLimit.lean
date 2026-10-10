import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicPartition

namespace OAI

/-! # Convergence of the growing original square sums -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped BigOperators Topology Classical

 theorem densitySquareIntegralTerm_summable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : Summable (densitySquareIntegralTerm χ s) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => densitySquareSeriesTerm_integrable χ s hs n)
    (densitySquareSeriesTerm_integral_summable χ s hs)
  exact h.summable.mul_left (2 * (Real.pi : ℂ))⁻¹

 @[simp] theorem densitySquareIntegralTerm_zero (χ : PrimitiveComplexCharacter) (s : ℂ) :
    densitySquareIntegralTerm χ s 0 = 0 := by
  simp [densitySquareIntegralTerm, densitySquareSeriesTerm]

 theorem densitySquare_partial_limit (χ : PrimitiveComplexCharacter) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) :
    Tendsto (fun J : ℕ => ∑ n ∈ Finset.Icc 1 (2 ^ J * N),
      densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n) atTop
        (𝓝 (densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t))) := by
  let s := densityVerticalPoint (1 / 2) t
  have hs : s.re = 1 / 2 := by simp [s, densityVerticalPoint]
  have hc : Tendsto (fun J : ℕ => 2 ^ J * N + 1) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
    intro J
    have h := Nat.le_mul_of_pos_right (2 ^ J) (by omega : 0 < N)
    omega
  have he (K : ℕ) : (∑ n ∈ Finset.Icc 1 K, densitySquareIntegralTerm χ s n) =
      ∑ n ∈ Finset.range (K + 1), densitySquareIntegralTerm χ s n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega)
    · intro n hn hnot
      have hn' := Finset.mem_range.mp hn
      have hzero : n = 0 := by
        by_contra hz
        exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      simp [hzero]
  have h := ((densitySquareIntegralTerm_summable χ s hs).hasSum.tendsto_sum_nat).comp hc
  rw [← densitySmoothedSquare_series χ s hs] at h
  change Tendsto (fun J => ∑ n ∈ Finset.range (2 ^ J * N + 1), densitySquareIntegralTerm χ s n)
    atTop (𝓝 (densitySmoothedSquare χ s)) at h
  exact h.congr' (Filter.Eventually.of_forall (fun J => (he (2 ^ J * N)).symm))

end Ostmann

end OAI
