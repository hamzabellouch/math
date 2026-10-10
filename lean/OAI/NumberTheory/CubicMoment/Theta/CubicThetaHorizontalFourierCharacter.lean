import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds

namespace OAI

/-! The actual horizontal additive character and its level-three period. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaHorizontalCharacter (h : Eisenstein) (z : ℂ) : ℂ :=
  Real.fourierChar (tracePair z (cubicThetaRowFrequency h))

lemma cubicThetaHorizontalCharacter_add (h : Eisenstein) (z w : ℂ) :
    cubicThetaHorizontalCharacter h (z+w)=
      cubicThetaHorizontalCharacter h z*cubicThetaHorizontalCharacter h w := by
  unfold cubicThetaHorizontalCharacter
  have he : tracePair (z+w) (cubicThetaRowFrequency h)=
      tracePair z (cubicThetaRowFrequency h)+tracePair w (cubicThetaRowFrequency h) := by
    simp only [tracePair,add_mul,Complex.add_re]
    ring
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma cubicThetaHorizontalCharacter_three (h w : Eisenstein) :
    cubicThetaHorizontalCharacter h (3*(w:ℂ))=1 := by
  have he : tracePair (3*(w:ℂ)) (cubicThetaRowFrequency h)=
      tracePair ((w*h:Eisenstein):ℂ) (1/traceLambda) := by
    unfold tracePair cubicThetaRowFrequency
    push_cast
    congr 2
    field_simp [traceLambda_ne_zero]
  change (Real.fourierChar (tracePair (3*(w:ℂ)) (cubicThetaRowFrequency h)):ℂ)=1
  rw [he,tracePhase_div_lambda_one]

lemma cubicThetaHorizontalCharacter_periodic (h w : Eisenstein) (z : ℂ) :
    cubicThetaHorizontalCharacter h (z+3*(w:ℂ))=cubicThetaHorizontalCharacter h z := by
  rw [cubicThetaHorizontalCharacter_add,cubicThetaHorizontalCharacter_three,mul_one]

lemma cubicThetaHorizontalCharacter_unit (h : Eisenstein) (z : ℂ) :
    star (cubicThetaHorizontalCharacter h z)*cubicThetaHorizontalCharacter h z=1 := by
  rw [mul_comm,Complex.star_def,Complex.mul_conj']
  change (‖(Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)‖:ℂ)^2=1
  simp

end CubicFirstMoment

end

end OAI
