import OAI.NumberTheory.CubicMoment.Estimates.FarHeightBound
import OAI.NumberTheory.CubicMoment.Estimates.HeightPolynomialIntegral
import OAI.NumberTheory.CubicMoment.Estimates.DyadicWeightIntegral

namespace OAI

/-! The actual far-cell height integral gains (J/T)^2. Its only analytic
coefficient bound is a uniform mean for the original finite polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

theorem far_integrated_norm_bound {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (h : ℝ → ℂ) (hi : Integrable h)
    (hd : Differentiable ℝ h) (hi' : Integrable (deriv h))
    (hd' : Differentiable ℝ (deriv h)) (hi'' : Integrable (deriv (deriv h)))
    {J T M R : ℝ} (hJ : 0 < J) (hT : 0 < T) (hM : 0 ≤ M) (x₀ : ℝ)
    (hfar : ∀ a ∈ S, 1 ≤ |J*(Real.log (norm (n a))-x₀)|)
    (hsecond : ∀ t, ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ M)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → deriv (deriv h) t = 0)
    (hmean : ∀ v : ℝ, dyadicHeightMean
      (fun t => ‖∑ a ∈ S, c a*normTwist (t+v) (n a)‖) T ≤ R) :
    ‖(T:ℂ)⁻¹*(∑ a ∈ S,
      c a*heightFourierIntegral h (Real.log (norm (n a))-x₀))‖ ≤
      (J/T)^2*M*R*(∫ u : ℝ, ‖𝓕 farInverseSquare u‖) := by
  let h₂ := fun t : ℝ => (T:ℂ)^2*deriv (deriv h) t
  let d := fun a => c a*farInverseSquare (J*(Real.log (norm (n a))-x₀))
  let f := fun t : ℝ => ∑ a ∈ S, d a*normTwist t (n a)
  let w := fun t : ℝ => h₂ t*Complex.exp ((-x₀*t:ℝ)*Complex.I)
  have he : (∑ a ∈ S, c a*heightFourierIntegral h (Real.log (norm (n a))-x₀)) =
      -((J/T:ℝ):ℂ)^2*(∑ a ∈ S, d a*heightFourierIntegral h₂ (Real.log (norm (n a))-x₀)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [far_height_identity h hi hd hi' hd' hi'' hJ hT (hfar a ha)]
    dsimp [d,h₂]
    ring
  have hf : Continuous f := continuous_indexed_norm_polynomial S d n
  have hwm : ∀ t, ‖w t‖ ≤ M := by
    intro t
    have hp : ‖Complex.exp ((-x₀*t:ℝ)*Complex.I)‖ = 1 := by simp [Complex.norm_exp]
    simpa only [w,h₂,norm_mul,hp,mul_one] using hsecond t
  have hws : ∀ t, t ∉ dyadicHeightSupport T → w t = 0 := by
    intro t ht
    simp only [w,h₂,hs t ht,mul_zero,zero_mul]
  have hb := normalized_dyadicWeightIntegral_bound f w hf hT hM hwm hws
  have hfarmean : dyadicHeightMean (fun t => ‖f t‖) T ≤
      R*(∫ u : ℝ, ‖𝓕 farInverseSquare u‖) := by
    have hm := far_norm_sum_height_bound S c n 0 x₀ hJ hT hmean
    have heq : (fun t : ℝ => ∑ a ∈ S, c a*normTwist (0+t) (n a)*
        farInverseSquare (J*(Real.log (norm (n a))-x₀))) = f := by
      funext t
      simp only [zero_add,f,d]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have hnorm := congrArg (fun F : ℝ → ℂ => fun t : ℝ => ‖F t‖) heq
    rwa [hnorm] at hm
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hfarmean hM)
  have hint : (∑ a ∈ S, d a*heightFourierIntegral h₂ (Real.log (norm (n a))-x₀)) =
      ∫ t : ℝ, w t*f t :=
    height_norm_polynomial_integral S d n h₂ (hi''.const_mul _) x₀
  rw [he,hint]
  have hscalar : ‖-((J/T:ℝ):ℂ)^2‖ = (J/T)^2 := by
    rw [norm_neg,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    ‖(T:ℂ)⁻¹*(-((J/T:ℝ):ℂ)^2*(∫ t : ℝ, w t*f t))‖ =
        (J/T)^2*‖(T:ℂ)⁻¹*(∫ t : ℝ, w t*f t)‖ := by
      rw [show (T:ℂ)⁻¹*(-((J/T:ℝ):ℂ)^2*(∫ t : ℝ, w t*f t)) =
        -((J/T:ℝ):ℂ)^2*((T:ℂ)⁻¹*(∫ t : ℝ, w t*f t)) by ring,norm_mul,hscalar]
    _ ≤ (J/T)^2*(M*(R*(∫ u : ℝ, ‖𝓕 farInverseSquare u‖))) :=
      mul_le_mul_of_nonneg_left hb' (sq_nonneg _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
