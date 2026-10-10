import OAI.Analysis.KadisonKastler.ThresholdCutIntegral

namespace OAI

/-! # Signed-square coordinates for spectral cuts

Passing from a spectral value x to x |x| absorbs the weight |t| in
Haagerup's spectral-cut integral. The estimates here are scalar.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

def signedSquare (x : ℝ) : ℝ := x*|x|

theorem abs_signedSquare (x : ℝ) : |signedSquare x|=x^2 := by
  rw [signedSquare,abs_mul,abs_abs,← sq,sq_abs]

theorem signedSquare_gap_le (x y : ℝ) :
    |signedSquare x-signedSquare y| ≤ |x-y| *(|x| +|y|) := by
  have he : signedSquare x-signedSquare y=x*(|x|-|y|)+(x-y)*|y| := by
    unfold signedSquare
    ring
  rw [he]
  calc
    _ ≤ abs (x*(|x|-|y|))+abs ((x-y)*|y|) := abs_add_le _ _
    _ = |x| * abs (|x|-|y|) + |x-y| * |y| := by rw [abs_mul,abs_mul,abs_abs]
    _ ≤ |x| *|x-y| +|x-y| *|y| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (abs_nonneg x)) le_rfl
    _ = _ := by ring

theorem sq_gap_le_signedSquare (x y : ℝ) :
    (x-y)^2 ≤ 2*|signedSquare x-signedSquare y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simp only [signedSquare,abs_of_nonneg hx,abs_of_nonneg hy]
    rcases le_total x y with hxy | hyx
    · have hs : x*x-y*y ≤ 0 := by nlinarith
      rw [abs_of_nonpos hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hx,sq_nonneg (x-y)]
    · have hs : 0 ≤ x*x-y*y := by nlinarith
      rw [abs_of_nonneg hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hyx) hy,sq_nonneg (x-y)]
  · simp only [signedSquare,abs_of_nonneg hx,abs_of_nonpos hy]
    have hs : 0 ≤ x*x-y*(-y) := by nlinarith [sq_nonneg x,sq_nonneg y]
    rw [abs_of_nonneg hs]
    nlinarith [sq_nonneg (x+y)]
  · simp only [signedSquare,abs_of_nonpos hx,abs_of_nonneg hy]
    have hs : x*(-x)-y*y ≤ 0 := by nlinarith [sq_nonneg x,sq_nonneg y]
    rw [abs_of_nonpos hs]
    nlinarith [sq_nonneg (x+y)]
  · simp only [signedSquare,abs_of_nonpos hx,abs_of_nonpos hy]
    rcases le_total x y with hxy | hyx
    · have hs : x*(-x)-y*(-y) ≤ 0 := by nlinarith
      rw [abs_of_nonpos hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (neg_nonneg.mpr hy),sq_nonneg (x-y)]
    · have hs : 0 ≤ x*(-x)-y*(-y) := by nlinarith
      rw [abs_of_nonneg hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (neg_nonneg.mpr hx),sq_nonneg (x-y)]

theorem outward_threshold_coefficient (x t : ℝ) :
    (if t < 0 then 1-(if t < signedSquare x then 1 else 0 : ℝ)
      else (if t < signedSquare x then 1 else 0 : ℝ)) =
        thresholdDifference (signedSquare x) 0 t ^ 2 := by
  by_cases ht : t < 0 <;> by_cases hx : t < signedSquare x <;>
    simp [thresholdDifference,ht,hx]

theorem integral_outward_threshold_coefficient (x : ℝ) :
    (∫ t, thresholdDifference (signedSquare x) 0 t ^ 2)=x^2 := by
  rw [integral_thresholdDifference_sq,sub_zero,abs_signedSquare]

end

end KadisonKastler

end OAI
