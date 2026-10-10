import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMomentDyadic

namespace OAI

/-! # The actual mollifier mean with a whole-line cubic height weight -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

 theorem density_weighted_mollifier_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      Integrable (fun t => densityHeightWeight T t * ∑ χ ∈ F,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ∧
      (∫ t, densityHeightWeight T t * ∑ χ ∈ F,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X) := by
  obtain ⟨C, hC, hb⟩ := density_mollifier_primitive_mean
  refine ⟨C * densityHeightEnergyConstant 0, mul_pos hC (densityHeightEnergyConstant_pos 0), ?_⟩
  intro X Q hX hQ T hT F hF
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hl0 : 0 ≤ Real.log X := Real.log_nonneg hx
  let A := C * ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log X)
  have hfχ (χ : PrimitiveComplexCharacter) :
      Continuous (fun t => ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) := by
    have h := density_mollifier_family_continuous {χ} X
    simpa using h
  have hball (j : ℕ) :
      (∫ t in densityHeightBall T j, ∑ χ ∈ F,
        ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2) ≤
          A * (2 : ℝ) ^ j * (j + 1 : ℝ) ^ 0 := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hH : 1 ≤ (2 : ℝ) ^ j * T := by nlinarith
    have hh := hb X Q hQ ((2 : ℝ) ^ j * T) hH F hF
    rw [densityHeightBall, integral_finsetSum F (fun χ _ => (hfχ χ).continuousOn.integrableOn_Icc)]
    apply hh.trans
    have hsize : (X : ℝ) + (Q : ℝ) ^ 2 * ((2 : ℝ) ^ j * T) ≤
        ((X : ℝ) + (Q : ℝ) ^ 2 * T) * (2 : ℝ) ^ j := by
      have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
      nlinarith
    calc
      _ ≤ C * (((X : ℝ) + (Q : ℝ) ^ 2 * T) * (2 : ℝ) ^ j) * (1 + Real.log X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hC.le) (by positivity)
      _ = _ := by dsimp [A]; ring
  obtain ⟨hi, hm⟩ := density_weighted_moment
    (fun t => ∑ χ ∈ F, ‖densityMollifier X χ.character (densityVerticalPoint (1 / 2) t)‖ ^ 2)
    (density_mollifier_family_continuous F X) (fun _ => Finset.sum_nonneg (fun _ _ => by positivity))
    T (by linarith) A (by dsimp [A]; positivity) 0 hball
  refine ⟨hi, hm.trans_eq ?_⟩
  dsimp [A]
  ring

end Ostmann

end OAI
