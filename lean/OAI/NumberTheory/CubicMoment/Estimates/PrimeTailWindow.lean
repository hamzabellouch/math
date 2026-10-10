import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailProductMellin
import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductWindow
import OAI.NumberTheory.CubicMoment.Estimates.SharpHeightMultiplier

namespace OAI

/-! The actual Fourier height window is bounded by its two-sided mean,
including the reciprocal height normalization and both endpoint phases. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma cutoffHeightWindow_integral_bound (f : ℝ → ℂ) (hf : Continuous f)
    (H X : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow T t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*f t‖ ≤
      2*dyadicHeightMean (fun t => ‖f t‖) T := by
  let w := fun t => cutoffHeightMultiplier H t*heightWindow T t*
    Complex.exp ((-Real.log X*t:ℝ)*Complex.I)
  have hs (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : w t = 0 := by
    simp only [w,heightWindow_zero hT ht,mul_zero,zero_mul]
  have hb (t : ℝ) : ‖w t‖ ≤ 2/T := by
    by_cases ht : t ∈ dyadicHeightSupport T
    · have ha : T ≤ |t| := by
        rcases ht with ht | ht
        · exact ht.1.trans (le_abs_self t)
        · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
      have hp : 0 < |t| := hT.trans_le ha
      simp only [w,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
      calc
        _ ≤ ‖cutoffHeightMultiplier H t‖*1 :=
          mul_le_mul_of_nonneg_left (heightWindow_norm_le T t) (_root_.norm_nonneg _)
        _ ≤ 2/|t| := by simpa only [mul_one] using cutoffHeightMultiplier_norm_le H (abs_pos.mp hp)
        _ ≤ 2/T := div_le_div_of_nonneg_left (by norm_num) hT ha
    · rw [hs t ht,norm_zero]
      positivity
  have he := dyadicWeightIntegral_bound f w hf hT (by positivity : 0 ≤ 2/T) hb hs
  change ‖∫ t : ℝ, w t*f t‖ ≤ _
  exact he.trans_eq (by field_simp)

def productGaussWindow (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) (H U X : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ S, α a*β b*productGaussHeightWindowKernel ℓ W H U X X (a*b)

lemma productGaussWindow_integral (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) {H : ℝ} (hH : 0 < H) (U X : ℝ) :
    productGaussWindow P S α β ℓ W H U X =
      ∫ t : ℝ, (cutoffHeightMultiplier H t*heightWindow U t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
          productGaussSmoothed P S α β ℓ W X t := by
  let c := fun q : Eisenstein × Eisenstein =>
    α q.1*β q.2*theta ℓ (q.1*q.2)*gauss (q.1*q.2)*W (norm (q.1*q.2)/X)
  have he := height_norm_polynomial_integral (P.product S) c (fun q => q.1*q.2)
    (fun t => cutoffHeightMultiplier H t*heightWindow U t)
    (integrable_cutoffHeightMultiplier_window hH U) (Real.log X)
  simp only [Finset.product_eq_sprod,Finset.sum_product] at he
  calc
    _ = ∑ a ∈ P, ∑ b ∈ S, c (a,b)*
        heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow U t)
          (Real.log (norm (a*b))-Real.log X) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp [productGaussWindow,productGaussHeightWindowKernel,c]
      ring
    _ = _ := by
      rw [he]
      congr 1
      funext t
      simp only [productGaussSmoothed,Finset.mul_sum,c]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma productGaussWindow_bound (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (ℓ : ℤ) (W : ℝ → ℂ) {H U : ℝ} (hH : 0 < H) (hU : 0 < U) (X : ℝ) :
    ‖productGaussWindow P S α β ℓ W H U X‖ ≤
      2*dyadicHeightMean (fun t => ‖productGaussSmoothed P S α β ℓ W X t‖) U := by
  rw [productGaussWindow_integral P S α β ℓ W hH U X]
  exact cutoffHeightWindow_integral_bound _
    (productGaussSmoothed_continuous P S α β ℓ W X) H X hU

end CubicFirstMoment

end

end OAI
