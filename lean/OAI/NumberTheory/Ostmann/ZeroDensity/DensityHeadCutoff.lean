import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteSquareMean
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityShiftedDivisorEnergy

namespace OAI

/-! # The logarithmic short contour for the actual finite head -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityKernelCost_log (N Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 1 ≤ T)
    (hN : 1 ≤ Real.log N) (hscale : 10 * (Q : ℝ) * T ≤ N) :
    densityKernelCost Q T (1 / Real.log N) ≤
      densityKernelConstant * Real.exp 1 * Real.log N := by
  have hNp : (0 : ℝ) < N := by
    have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have hB : 0 < 10 * (Q : ℝ) * T := by positivity
    exact hB.trans_le hscale
  have hc : 0 < 1 / Real.log N := div_pos zero_lt_one (by linarith)
  have hpow : (N : ℝ) ^ (1 / Real.log N) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hNp]
    congr 1
    field_simp
  unfold densityKernelCost
  calc
    _ ≤ densityKernelConstant * (N : ℝ) ^ (1 / Real.log N) / (1 / Real.log N) := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hscale hc.le) densityKernelConstant_pos.le
    _ = _ := by rw [hpow]; field_simp

 theorem densityFiniteSquare_head_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      1 ≤ Real.log N → 10 * (Q : ℝ) * T ≤ N →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ Finset.Icc 1 N,
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_mean
  refine ⟨16 * C * (densityKernelConstant * Real.exp 1) ^ 2, by
    have := densityKernelConstant_pos
    positivity, ?_⟩
  intro N Q hQ T hT hN hscale F hF
  let c : ℝ := 1 / Real.log N
  have hc : 0 < c := div_pos zero_lt_one (by linarith)
  have hc1 : c ≤ 1 := by dsimp [c]; exact (div_le_one (by linarith)).mpr hN
  have h := hb N Q hQ T c hT hc hc1 (Finset.Icc 1 N) (fun _ hn => hn) F hF
  have he := density_divisor_shifted_head N c hc.le
  have hk := densityKernelCost_log N Q hQ T hT hN hscale
  have hlog : (1 + Real.log N) ^ 4 ≤ 16 * (Real.log N) ^ 4 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log N)
      (by linarith : 1 + Real.log N ≤ 2 * Real.log N) 4
    nlinarith
  calc
    _ ≤ C * (densityKernelCost Q T c) ^ 2 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
        (1 + Real.log N) ^ 4 := h.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ C * (densityKernelConstant * Real.exp 1 * Real.log N) ^ 2 *
        ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (16 * (Real.log N) ^ 4) := by
      apply mul_le_mul _ hlog (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (densityKernelCost_pos Q hQ T c hT hc).le hk 2) hC.le
    _ = _ := by ring

end Ostmann

end OAI
