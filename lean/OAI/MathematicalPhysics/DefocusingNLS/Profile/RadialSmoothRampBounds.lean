import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmoothRamp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Bounds for the smoothed core/shell transition used in the inner fixed point. -/

namespace DefocusingNLS

theorem radialSmoothRamp_bounds (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    0 ≤ radialSmoothRamp δ x ∧ radialSmoothRamp δ x ≤ (max x 0)^2 ∧
    0 ≤ radialSmoothRampD δ x ∧ radialSmoothRampD δ x ≤ 2*max x 0 ∧
    0 ≤ radialSmoothRampDD δ x ∧ radialSmoothRampDD δ x ≤ 2 := by
  by_cases hx : x ≤ 0
  · simp only [radialSmoothRamp,radialSmoothRampD,radialSmoothRampDD,radialSplice,
      ite_eq_left hx,max_eq_right hx]
    norm_num
  · have hx0 : 0 < x := lt_of_not_ge hx
    by_cases hxd : x ≤ δ
    · simp only [radialSmoothRamp,radialSmoothRampD,radialSmoothRampDD,
        radialRampInner,radialRampInnerD,radialRampInnerDD,radialSplice,
        ite_eq_right hx,ite_eq_left hxd,max_eq_left hx0.le]
      refine ⟨by positivity,?_,by positivity,?_,by positivity,?_⟩
      · apply (div_le_iff₀ (by positivity : 0 < 3*δ)).2
        nlinarith [mul_le_mul_of_nonneg_right hxd (sq_nonneg x)]
      · apply (div_le_iff₀ hδ).2
        nlinarith [mul_le_mul_of_nonneg_right hxd hx0.le]
      · apply (div_le_iff₀ hδ).2
        linarith
    · have hdx : δ < x := lt_of_not_ge hxd
      simp only [radialSmoothRamp,radialSmoothRampD,radialSmoothRampDD,
        radialRampInner,radialRampInnerD,radialRampInnerDD,radialSplice,
        ite_eq_right hx,ite_eq_right hxd,max_eq_left hx0.le]
      have hprod : δ^2 ≤ δ*x := by nlinarith [mul_le_mul_of_nonneg_left hdx.le hδ.le]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right hdx.le hx0.le,sq_nonneg δ]
      · refine ⟨?_,?_,?_,by norm_num,by norm_num⟩ <;> nlinarith

theorem monotone_radialSmoothRamp (δ : ℝ) (hδ : 0 < δ) :
    Monotone (radialSmoothRamp δ) := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (hasDerivAt_radialSmoothRamp δ hδ x).differentiableAt
  · intro x
    rw [(hasDerivAt_radialSmoothRamp δ hδ x).deriv]
    exact (radialSmoothRamp_bounds δ hδ x).2.2.1

end DefocusingNLS

end OAI
