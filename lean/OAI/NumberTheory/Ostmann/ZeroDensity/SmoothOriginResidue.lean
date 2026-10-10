import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothLocalContour
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterTrivialZero
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedSmoothExplicitFormula

namespace OAI

/-! # Identification of the literal even-character residue at zero -/

namespace Ostmann

open Filter
open scoped Topology Classical

theorem smoothContour_origin_residue_value (χ : PrimitiveComplexCharacter)
    (X : ℝ) :
    -(analyticOrderNatAt χ.L 0 : ℂ) * smoothContourWeight X 0 = -smoothTrivialZeroTerm χ := by
  rw [χ.L_multiplicity_at_zero]
  by_cases hχ : χ.character (-1) = 1
  · simp [hχ, smoothContourWeight, smoothTrivialZeroTerm]
  · simp [hχ, smoothTrivialZeroTerm]

theorem smoothContour_origin_residue (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) :
    Tendsto (fun s => s * ((-deriv χ.L s / χ.L s) * smoothContourWeight X s)) (𝓝[≠] 0)
      (𝓝 (-smoothTrivialZeroTerm χ)) := by
  simpa only [sub_zero, smoothContour_origin_residue_value] using
    smoothContour_zero_residue χ X hX 0

theorem smoothContour_origin_circle (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) :
    ∃ r : ℝ, 0 < r ∧
      (∮ s in C(0, r), (-deriv χ.L s / χ.L s) * smoothContourWeight X s) =
        -(2 * (Real.pi : ℂ) * Complex.I) * smoothTrivialZeroTerm χ := by
  obtain ⟨r, hr, hc⟩ := smoothContour_small_circle χ X hX 0
  refine ⟨r, hr, ?_⟩
  rw [smoothContour_origin_residue_value] at hc
  simpa only [mul_neg, neg_mul] using hc

end Ostmann

end OAI
