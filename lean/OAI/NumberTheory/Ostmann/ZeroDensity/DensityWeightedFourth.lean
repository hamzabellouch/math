import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMomentDyadic

namespace OAI

/-! # The actual fourth moment with a whole-line cubic height weight -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

 theorem density_weighted_fourth_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      Integrable (fun t => densityHeightWeight T t *
        ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ∧
      (∫ t, densityHeightWeight T t *
        ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
          C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := density_fourth_moment
  refine ⟨C * densityHeightEnergyConstant 6, mul_pos hC (densityHeightEnergyConstant_pos 6), ?_⟩
  intro Q hQ T hT F hF
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hl0 : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  let A := C * ((Q : ℝ) ^ 2 * T) * (Real.log ((Q : ℝ) * T)) ^ 6
  have hball (j : ℕ) :
      (∫ t in densityHeightBall T j, ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4) ≤
        A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ 6 := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hH : 2 ≤ (2 : ℝ) ^ j * T := by nlinarith
    have hh := hb Q hQ ((2 : ℝ) ^ j * T) hH F hF
    rw [densityHeightBall, integral_finsetSum F (fun χ _ =>
      density_L_fourth_integrable χ ((2 : ℝ) ^ j * T))]
    apply hh.trans
    have hlog := density_dyadic_height_log Q hQ T hT j
    have hlog0 : 0 ≤ Real.log ((Q : ℝ) * ((2 : ℝ) ^ j * T)) :=
      Real.log_nonneg (by nlinarith)
    calc
      _ ≤ C * ((Q : ℝ) ^ 2 * ((2 : ℝ) ^ j * T)) *
          ((j + 1 : ℝ) * Real.log ((Q : ℝ) * T)) ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 6) (by positivity)
      _ = _ := by dsimp [A]; ring
  obtain ⟨hi, hm⟩ := density_weighted_moment
    (fun t => ∑ χ ∈ F, ‖χ.L (densityVerticalPoint (1 / 2) t)‖ ^ 4)
    (density_L_fourth_family_continuous F) (fun _ => Finset.sum_nonneg (fun _ _ => by positivity))
    T (by linarith) A (by dsimp [A]; positivity) 6 hball
  refine ⟨hi, hm.trans_eq ?_⟩
  dsimp [A]
  ring

end Ostmann

end OAI
