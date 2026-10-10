import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourLimit

namespace OAI

/-! # The actual smooth explicit formula with its left-contour remainder -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

/-- The exact contour remainder. A faithful numbering of the actual zero
multiplicities is the only enumeration data used in the formula. -/
theorem smooth_explicit_identity (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 2 ≤ X) :
    smoothMangoldtMean χ.modulus χ.character X +
      (∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i) +
      smoothTrivialZeroTerm χ =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, leftContourIntegrand χ X y := by
  let R := ∫ y : ℝ, rightContourIntegrand χ X y
  let L := ∫ y : ℝ, leftContourIntegrand χ X y
  let S := ∑' i, smoothZeroTerm (fun ψ => characterZeroEnumeration ψ (e ψ)) χ X i
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hcont := smooth_contour_limit e χ X hX
  change I * R - I * L = -(2 * (Real.pi : ℂ) * I) * (S + smoothTrivialZeroTerm χ) at hcont
  have hrel : R - L = -(2 * (Real.pi : ℂ)) * (S + smoothTrivialZeroTerm χ) := by
    apply mul_left_cancel₀ (show (I : ℂ) ≠ 0 by simp)
    calc
      I * (R - L) = I * R - I * L := mul_sub _ _ _
      _ = _ := hcont
      _ = _ := by ring
  have hc : c * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp [c]
    push_cast
    field_simp
  have hmean : smoothMangoldtMean χ.modulus χ.character X = c * R :=
    smoothMangoldtMean_eq_vertical_logDerivative χ X (by linarith)
  have hsum : R + (2 * (Real.pi : ℂ)) * (S + smoothTrivialZeroTerm χ) = L := by
    linear_combination hrel
  change smoothMangoldtMean χ.modulus χ.character X + S + smoothTrivialZeroTerm χ = c * L
  rw [hmean, ← hsum, mul_add, ← mul_assoc, hc, one_mul]
  ring

end Ostmann

end OAI
