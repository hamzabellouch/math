import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegerBox
import OAI.NumberTheory.CubicGram.Coordinates

namespace OAI

/-! Square-root norm bounds outside finite coordinate boxes. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaIntegerQuadratic (p : CubicThetaIntegerPoint) : ℝ :=
  (p.1:ℝ)^2-(p.1:ℝ)*(p.2:ℝ)+(p.2:ℝ)^2

def cubicThetaPrimaryQuadratic (p : CubicThetaIntegerPoint) : ℝ :=
  (1+3*(p.1:ℝ))^2-(1+3*(p.1:ℝ))*(3*(p.2:ℝ))+(3*(p.2:ℝ))^2

lemma cubicThetaIntAbs_cast (i : ℤ) : (i.natAbs:ℝ)=|(i:ℝ)| := by
  have h := congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs i)
  simpa only [Int.cast_natCast,Int.cast_abs] using h

lemma cubicThetaQuadratic_nonneg (x y : ℝ) : 0≤x^2-x*y+y^2 := by
  nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]

lemma cubicThetaQuadratic_lower (x y : ℝ) :
    (3/4:ℝ)*x^2≤x^2-x*y+y^2 ∧ (3/4:ℝ)*y^2≤x^2-x*y+y^2 := by
  constructor <;> nlinarith [sq_nonneg (x-2*y),sq_nonneg (2*x-y)]

lemma cubicThetaIntegerQuadratic_sqrt_lower (p : CubicThetaIntegerPoint) :
    (6/7:ℝ)*cubicThetaIntegerRadius p≤Real.sqrt (cubicThetaIntegerQuadratic p) := by
  apply (Real.le_sqrt (by positivity) (cubicThetaQuadratic_nonneg _ _)).mpr
  unfold cubicThetaIntegerRadius
  rcases le_total p.2.natAbs p.1.natAbs with h | h
  · rw [max_eq_left h,cubicThetaIntAbs_cast]
    have hq := (cubicThetaQuadratic_lower (p.1:ℝ) p.2).1
    nlinarith [sq_abs (p.1:ℝ)]
  · rw [max_eq_right h,cubicThetaIntAbs_cast]
    have hq := (cubicThetaQuadratic_lower (p.1:ℝ) p.2).2
    nlinarith [sq_abs (p.2:ℝ)]

lemma cubicThetaPrimaryQuadratic_sqrt_lower (p : CubicThetaIntegerPoint)
    (hp : 2≤cubicThetaIntegerRadius p) :
    2*(cubicThetaIntegerRadius p:ℝ)≤Real.sqrt (cubicThetaPrimaryQuadratic p) := by
  apply (Real.le_sqrt (by positivity) (cubicThetaQuadratic_nonneg _ _)).mpr
  have hpR : (2:ℝ)≤cubicThetaIntegerRadius p := by exact_mod_cast hp
  unfold cubicThetaIntegerRadius at hpR ⊢
  rcases le_total p.2.natAbs p.1.natAbs with h | h
  · rw [max_eq_left h,cubicThetaIntAbs_cast] at hpR ⊢
    have hq := (cubicThetaQuadratic_lower (1+3*(p.1:ℝ)) (3*(p.2:ℝ))).1
    have hprod := mul_nonneg (abs_nonneg (p.1:ℝ)) (show 0≤|(p.1:ℝ)|-2 by linarith)
    have hi := neg_abs_le (p.1:ℝ)
    nlinarith [sq_abs (p.1:ℝ)]
  · rw [max_eq_right h,cubicThetaIntAbs_cast] at hpR ⊢
    have hq := (cubicThetaQuadratic_lower (1+3*(p.1:ℝ)) (3*(p.2:ℝ))).2
    nlinarith [sq_abs (p.2:ℝ)]

end CubicFirstMoment

end

end OAI
