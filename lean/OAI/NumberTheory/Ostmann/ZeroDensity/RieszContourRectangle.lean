import OAI.NumberTheory.Ostmann.ZeroDensity.RieszVerticalWeight
import OAI.NumberTheory.Ostmann.ZeroDensity.RectangleGeometry
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroMultiplicity

namespace OAI

/-! # The finite Riesz contour displacement when the rectangle is zero-free -/

namespace Ostmann

open Complex Set
open scoped Interval

noncomputable def rieszContourWeight (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * rieszMellinKernel s

theorem rieszContourWeight_analyticAt (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (rieszContourWeight X) s := by
  exact ((differentiable_id.const_cpow (.inl (by exact_mod_cast hX.ne'))).analyticAt s).mul
    (rieszMellinKernel_analyticAt_pos s hs)

theorem rieszContour_rectangle_zero (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hne : ∀ s ∈ uIcc a b ×ℂ uIcc c d, χ.L s ≠ 0) :
    rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s)
      a b c d = 0 := by
  apply rectangleBoundaryIntegral_eq_zero
  intro s hs
  have hspos : 0 < s.re := ha.trans_le ((uIcc_of_le hab) ▸ hs.1).1
  have hl : AnalyticAt ℂ (fun s => -logDeriv χ.L s) s := by
    exact ((χ.L_analytic s).deriv.div (χ.L_analytic s) (hne s hs)).neg
  exact hl.mul (rieszContourWeight_analyticAt X hX s hspos)

end Ostmann

end OAI
