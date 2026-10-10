import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteSquareMean
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityShiftedDivisorEnergy

namespace OAI

/-! # The original finite square on a distant coefficient block -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_tail_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ M N Q : ℕ, 1 ≤ M → 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc M N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ S, densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * (10 * (Q : ℝ) * T) ^ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
            ((N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ 3) := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_mean
  refine ⟨C * densityKernelConstant ^ 2, mul_pos hC (sq_pos_of_pos densityKernelConstant_pos), ?_⟩
  intro M N Q hM hQ T hT S hS F hF
  have hSN : S ⊆ Finset.Icc 1 N := fun n hn =>
    Finset.mem_Icc.mpr ⟨hM.trans (Finset.mem_Icc.mp (hS hn)).1, (Finset.mem_Icc.mp (hS hn)).2⟩
  have h := hb N Q hQ T 1 hT (by norm_num) (by norm_num) S hSN F hF
  have he := density_divisor_shifted_tail S M N hM hS
  have hbound := h.trans (mul_le_mul_of_nonneg_left he (by positivity))
  convert hbound using 1
  simp only [densityKernelCost, Real.rpow_one, div_one]
  ring

end Ostmann

end OAI
