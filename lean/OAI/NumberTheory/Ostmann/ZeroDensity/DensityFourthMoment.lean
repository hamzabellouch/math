import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySmoothedMean
import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareConjugation
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMomentCutoff

namespace OAI

/-! # The actual primitive-character fourth moment for the density argument -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem density_L_fourth_integrable (χ : PrimitiveComplexCharacter) (T : ℝ) :
    Integrable (fun t => ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4)
      (volume.restrict (Icc (-T) T)) := by
  have hL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  have hs : Continuous (fun t : ℝ => densityVerticalPoint (1 / 2) t) := by
    unfold densityVerticalPoint
    fun_prop
  exact (((hL.comp hs).norm.pow 4).continuousOn).integrableOn_Icc

 theorem density_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
          C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := densitySmoothedSquare_mean
  refine ⟨4 * C * 17 * 5 ^ 6, by positivity, ?_⟩
  intro Q hQ T hT F hF
  obtain ⟨N, hN, hL, hscale, hsize, hlog⟩ := density_moment_cutoff Q hQ T hT
  obtain ⟨hi, hm⟩ := hb N Q hN hQ T (by linarith) hL hscale F hF
  have hfirst : (∑ χ ∈ F, ∫ t in Icc (-T) T,
      ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
      4 * (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densitySmoothedSquare χ (densityVerticalPoint (1 / 2) t)‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    rw [← integral_const_mul]
    apply integral_mono (density_L_fourth_integrable χ T) ((hi χ hχ).const_mul 4)
    intro t
    exact density_L_fourth_single_bound χ _ (by simp [densityVerticalPoint])
  have hlog0 : 0 ≤ Real.log ((Q : ℝ) * T) := by
    apply Real.log_nonneg
    have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  calc
    _ ≤ 4 * (C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (Real.log N) ^ 6) :=
      hfirst.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
    _ ≤ 4 * (C * (17 * ((Q : ℝ) ^ 2 * T)) *
        (5 * Real.log ((Q : ℝ) * T)) ^ 6) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul _ (pow_le_pow_left₀ (by linarith) hlog 6) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsize) hC.le
    _ = _ := by ring

end Ostmann

end OAI
