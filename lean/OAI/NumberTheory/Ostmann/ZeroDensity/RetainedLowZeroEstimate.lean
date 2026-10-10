import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexLowZeroBound

namespace OAI

/-! # The retained low-zero sum, derived from two published inputs -/

namespace Ostmann
open scoped Classical BigOperators

theorem retained_low_zero_estimate (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ Q : ℕ, 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ F : Finset PrimitiveComplexCharacter,
        (∀ χ ∈ F, χ.modulus ≤ Q) →
        (∀ χ ∈ F, some χ ≠ exception) →
        ∀ M : ℝ, 12 * Real.log ((Q : ℝ) ^ 2 * T) ≤ M →
        (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices T).filter
          (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
            Real.exp (-M * (1 - ((Z χ).zeros i).re))) ≤
          2 * (C * (Real.log ((Q : ℝ) * T)) ^ 13) ^ 2 *
            Real.exp (-(M * (c / Real.log (2 * (Q : ℝ) * T))) / 2) := by
  obtain ⟨C, hC, hD⟩ := hD
  obtain ⟨c, hc, hR⟩ := hR
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q hQ T hT
  obtain ⟨exception, hexc⟩ := hR Q hQ T hT
  refine ⟨exception, ?_⟩
  intro F hF hFE M hM
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hbase : 1 ≤ (Q : ℝ) ^ 2 * T := by nlinarith
  have hlog : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hden : 0 < Real.log (2 * (Q : ℝ) * T) := Real.log_pos (by nlinarith)
  apply low_zero_laplace_bound Z F T
    (3 * Real.log ((Q : ℝ) ^ 2 * T))
    (C * (Real.log ((Q : ℝ) * T)) ^ 13) M
    (c / Real.log (2 * (Q : ℝ) * T))
  · exact mul_nonneg (by norm_num) (Real.log_nonneg hbase)
  · exact mul_nonneg hC.le (pow_nonneg hlog _)
  · linarith
  · exact (div_pos hc hden).le
  · intro χ hχ i hi
    exact hexc χ (hF χ hχ) (hFE χ hχ) i
      (((Z χ).mem_heightIndices T i).mp hi)
  · intro y hy hy'
    exact complex_zero_density_exponential Z hC.le hD Q (by omega) T y hT hy hy' F hF

end Ostmann

end OAI
