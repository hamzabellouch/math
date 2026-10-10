import OAI.NumberTheory.CubicMoment.Estimates.HeightPolynomialIntegral

namespace OAI

/-! The literal normalized height-integrated Gauss bilinear form. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def heightBilinearValue (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (h : ℝ → ℂ) (X₀ T : ℝ) : ℂ :=
  (T:ℂ)⁻¹*(∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
    heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀))

lemma heightBilinearValue_eq_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (h : ℝ → ℂ) (hi : Integrable h) (X₀ T : ℝ) :
    heightBilinearValue P S α β h X₀ T = (T:ℂ)⁻¹*
      ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist t (a*b) := by
  unfold heightBilinearValue
  congr 1
  calc
    _ = ∑ q ∈ P.product S, (α q.1*β q.2*gauss (q.1*q.2))*
        heightFourierIntegral h (Real.log (norm (q.1*q.2))-Real.log X₀) :=
      (Finset.sum_product P S _).symm
    _ = ∫ t : ℝ, (h t*Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I))*
        ∑ q ∈ P.product S, α q.1*β q.2*gauss (q.1*q.2)*normTwist t (q.1*q.2) :=
      height_norm_polynomial_integral _ _ _ h hi _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      exact Finset.sum_product P S _

end CubicFirstMoment

end

end OAI
