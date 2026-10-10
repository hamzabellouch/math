import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCompletedSquare
import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleAnalyticPole

namespace OAI

/-! # The Gaussian contour for the actual completed square -/

namespace Ostmann

open Complex

noncomputable def densitySquareGaussian (χ : PrimitiveComplexCharacter) (s w : ℂ) : ℂ :=
  densityCompletedSquare χ (s + w) * Complex.exp (w ^ 2)

 theorem densitySquareGaussian_analytic (χ : PrimitiveComplexCharacter) (s w : ℂ) :
    AnalyticAt ℂ (densitySquareGaussian χ s) w := by
  exact ((densityCompletedSquare_analytic χ (s + w)).comp
    (analyticAt_const.add analyticAt_id)).mul ((analyticAt_id.pow 2).cexp)

 theorem densitySquareGaussian_reflection (χ : PrimitiveComplexCharacter) (s w : ℂ) :
    densitySquareGaussian χ s (-w) =
      (@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character) ^ 2 *
        densitySquareGaussian χ.inverse (1 - s) w := by
  rw [densitySquareGaussian, densityCompletedSquare_reflection]
  simp only [neg_sq, densitySquareGaussian]
  rw [show 1 - (s + -w) = (1 - s) + w by ring]
  ring

 theorem densitySquareGaussian_rectangle (χ : PrimitiveComplexCharacter) (s : ℂ)
    (a b T : ℝ) (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    rectangleBoundaryIntegral (fun w => densitySquareGaussian χ s w / w) a b (-T) T =
      (2 * (Real.pi : ℂ) * I) * densityCompletedSquare χ s := by
  have h := rectangle_analytic_pole (densitySquareGaussian χ s) a b (-T) T ha hb
    (by linarith) hT (fun w _ => densitySquareGaussian_analytic χ s w)
  simpa only [densitySquareGaussian, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    Complex.exp_zero, mul_one] using h

 theorem densitySquareGaussian_normalized (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (hs : 0 < s.re) (hsw : 0 < (s + w).re) :
    densitySquareGaussian χ s w / densitySquareNormalizer χ s =
      densityCompletedSquareWeight χ s w * χ.L (s + w) ^ 2 := by
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hp : (χ.modulus : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hg : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro he
    exact χ.gammaInverse_ne_zero s hs
      (by simp only [PrimitiveComplexCharacter.gammaInverse, he, inv_zero])
  rw [densitySquareGaussian, densityCompletedSquare_eq χ (s + w) hsw,
    Complex.cpow_add _ _ hq]
  unfold densitySquareNormalizer densityCompletedSquareWeight
  field_simp

end Ostmann

end OAI
