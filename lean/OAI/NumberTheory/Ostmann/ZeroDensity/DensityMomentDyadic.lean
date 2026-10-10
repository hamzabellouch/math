import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourthMoment
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityWeightedMoment
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierMean
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorAnalytic

namespace OAI

/-! # Dyadic height bounds for the actual fourth and mollifier moments -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

 theorem density_dyadic_height_log (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) (j : ℕ) :
    Real.log ((Q : ℝ) * ((2 : ℝ) ^ j * T)) ≤
      (j + 1 : ℝ) * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hqt : 0 < (Q : ℝ) * T := by positivity
  have hl : Real.log 2 ≤ Real.log ((Q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  calc
    _ = (j : ℝ) * Real.log 2 + Real.log ((Q : ℝ) * T) := by
      rw [show (Q : ℝ) * ((2 : ℝ) ^ j * T) = (2 : ℝ) ^ j * ((Q : ℝ) * T) by ring,
        Real.log_mul (by positivity) hqt.ne', Real.log_pow]
    _ ≤ (j : ℝ) * Real.log ((Q : ℝ) * T) + Real.log ((Q : ℝ) * T) :=
      add_le_add (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg j)) le_rfl
    _ = _ := by ring

 theorem density_L_fourth_family_continuous (F : Finset PrimitiveComplexCharacter) :
    Continuous (fun t => ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) := by
  apply continuous_finsetSum
  intro χ _
  have hL : Continuous χ.L := continuous_iff_continuousAt.mpr (fun z => (χ.L_analytic z).continuousAt)
  exact ((hL.comp (by unfold densityVerticalPoint; fun_prop)).norm.pow 4)

 theorem density_mollifier_family_continuous (F : Finset PrimitiveComplexCharacter) (X : ℕ) :
    Continuous (fun t => ∑ χ ∈ F,
      ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) := by
  apply continuous_finsetSum
  intro χ _
  have hM : Continuous (densityMollifier X χ.character) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [zero_add] using (densityMollifier_shift_analytic χ X 0 z).continuousAt
  exact ((hM.comp (by unfold densityVerticalPoint; fun_prop)).norm.pow 2)

 theorem density_mollifier_primitive_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hb⟩ := critical_mollifier_mean
  refine ⟨C, hC, ?_⟩
  intro X Q hQ T hT F hF
  rw [densityCharacterFamily_sum F Q hF (fun q χ => ∫ t in Icc (-T) T,
    ‖densityMollifier X χ (densityVerticalPoint (1 / 2) t)‖ ^ 2)]
  exact hb X Q hQ T hT (densityCharacterFamily F)
    (fun q _ χ hχ => densityCharacterFamily_primitive F q χ hχ)

end Ostmann

end OAI
