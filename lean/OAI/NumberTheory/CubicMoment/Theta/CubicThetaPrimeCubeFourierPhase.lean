import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeGauss
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds

namespace OAI

/-! Exact additive phase separation on the triangularized branches.
The finite character has the same codifferent and sign as the original
horizontal Fourier expansion. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeFourierPhase {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h b : Eisenstein) (z : ℂ) :
    (Real.fourierChar (tracePair
      ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*z+(3:ℂ)*(b:ℂ)/(p:ℂ)^(3-k.val))
      (cubicThetaRowFrequency h)) : ℂ)=
      (Real.fourierChar (tracePair z
        ((p:ℂ)^k.val/(p:ℂ)^(3-k.val)*cubicThetaRowFrequency h)) : ℂ)*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) (h*b)) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  let a := (p:ℂ)^k.val/(p:ℂ)^(3-k.val)
  have he : (a*z+(3:ℂ)*(b:ℂ)/(p:ℂ)^(3-k.val))*cubicThetaRowFrequency h=
      z*(a*cubicThetaRowFrequency h)+((h*b:Eisenstein):ℂ)*
        (1/(((p^(3-k.val):Eisenstein):ℂ)*traceLambda)) := by
    unfold cubicThetaRowFrequency
    push_cast
    field_simp [a,traceLambda_ne_zero]
  have ht : tracePair (a*z+(3:ℂ)*(b:ℂ)/(p:ℂ)^(3-k.val)) (cubicThetaRowFrequency h)=
      tracePair z (a*cubicThetaRowFrequency h)+
        tracePair ((h*b:Eisenstein):ℂ) (1/(((p^(3-k.val):Eisenstein):ℂ)*traceLambda)) := by
    unfold tracePair
    rw [he,Complex.add_re]
    ring
  rw [residueFourierChar_mk]
  change (Real.fourierChar (tracePair (a*z+(3:ℂ)*(b:ℂ)/(p:ℂ)^(3-k.val))
    (cubicThetaRowFrequency h)) : ℂ)=_
  rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul]

end CubicFirstMoment

end

end OAI
