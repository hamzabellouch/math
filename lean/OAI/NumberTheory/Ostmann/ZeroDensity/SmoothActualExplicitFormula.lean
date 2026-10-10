import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothExplicitIdentity
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothZeroCountFamily

namespace OAI

/-! # Discharging the fixed-test smooth explicit-formula input -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

theorem actual_smooth_explicit_formula (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (χ : PrimitiveComplexCharacter) (X : ℝ), 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
          smoothTrivialZeroTerm χ‖ ≤ E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ)) := by
  obtain ⟨E, hE, hbound⟩ := leftContour_integral_bound
  refine ⟨E, hE, ?_⟩
  intro χ X hX
  rw [smooth_explicit_identity e χ X hX, norm_mul]
  have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hbound χ X (by linarith))

noncomputable def actualSmoothExplicitFormula (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ) :
    PublishedSmoothExplicitFormula (fun χ => characterZeroEnumeration χ (e χ)) := by
  let E := Classical.choose (actual_smooth_explicit_formula e)
  have hE := (Classical.choose_spec (actual_smooth_explicit_formula e)).1
  have hformula := (Classical.choose_spec (actual_smooth_explicit_formula e)).2
  exact smoothExplicitFormula_of_multiplicity
    (fun χ => characterZeroEnumeration_respectsMultiplicity χ (e χ)) E hE hformula

end Ostmann

end OAI
