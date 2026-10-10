import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothExplicitFormulaCore
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimitiveCharacterCard

namespace OAI

/-! # The ordinary individual zero count supplies the family count -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

theorem family_zero_count_of_individual {Z : ∀ χ, ComplexZeroEnumeration χ}
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ χ : PrimitiveComplexCharacter, ∀ T : ℝ, 0 ≤ T →
      ((Z χ).count 0 T : ℝ) ≤ C * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)))
    (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 0 ≤ T)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    (∑ χ ∈ F, ((Z χ).count 0 T : ℝ)) ≤
      C * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog : 0 ≤ Real.log ((Q : ℝ) * (T + 2)) :=
    Real.log_nonneg (by nlinarith)
  have hB : 0 ≤ C * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by positivity
  calc
    _ ≤ ∑ χ ∈ F, C * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
      apply sum_le_sum
      intro χ hχ
      apply (hcount χ T hT).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.log_le_log (mul_pos (by exact_mod_cast χ.positive) (by linarith))
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hF χ hχ) (by linarith)
    _ = (F.card : ℝ) * (C * (T + 1) * Real.log ((Q : ℝ) * (T + 2))) := by simp
    _ ≤ (Q : ℝ) ^ 2 * (C * (T + 1) * Real.log ((Q : ℝ) * (T + 2))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast primitive_character_family_card F Q hF) hB
    _ = _ := by ring

/-- Only the ordinary individual count and the explicit formula are needed.
The family count, Mellin decay and absolute convergence are already proved. -/
noncomputable def smoothExplicitFormula_of_individual {Z : ∀ χ, ComplexZeroEnumeration χ}
    (E C : ℝ) (hE : 0 < E) (hC : 0 < C)
    (hcount : ∀ χ : PrimitiveComplexCharacter, ∀ T : ℝ, 0 ≤ T →
      ((Z χ).count 0 T : ℝ) ≤ C * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)))
    (hformula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
          E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))) :
    PublishedSmoothExplicitFormula Z :=
  SmoothExplicitFormulaCore.toPublished {
    errorConstant := E
    errorConstant_pos := hE
    zeroCountConstant := C
    zeroCountConstant_pos := hC
    zero_count := family_zero_count_of_individual C hC.le hcount
    explicit_formula := hformula
  }

end Ostmann

end OAI
