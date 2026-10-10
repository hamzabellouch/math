import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStep
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedFiniteFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitCharacterFourier

namespace OAI

/-! Explicit additive character at an integral translated cusp. Its
frequency is determined by the omega coordinate of the translation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCuspCharacter (b : Eisenstein) : AddChar Eisenstein ℂ where
  toFun := cubicThetaCuspStepValue b
  map_zero_eq_one' := by
    simpa only [mul_zero] using cubicThetaCuspStepValue_triple b 0
  map_add_eq_mul' := cubicThetaCuspStepValue_add b

lemma cubicThetaCuspCharacter_one (b : Eisenstein) :
    cubicThetaCuspCharacter b 1=(cubicThetaRamifiedCharacter (-b))^2 := by
  have hp : primary (1-3*b) := ⟨-b,by ring⟩
  change (if (-3*(1:Eisenstein))=0 then 1 else cubicSymbol (1-3*b*1) (-3*1))=_
  norm_num only [mul_one,neg_ne_zero,OfNat.ofNat_ne_zero,ite_false]
  rw [cubicSymbol_neg hp,cubicThetaSymbol_three hp,show 1-3*b=1+3*(-b) by ring]
  rfl

lemma cubicThetaCuspCharacter_omega (b : Eisenstein) :
    cubicThetaCuspCharacter b omegaE=
      (cubicThetaRamifiedCharacter (-b*omegaE))^2*cubicThetaUnitCharacter (-b*omegaE) := by
  have hp : primary (1-3*b*omegaE) := ⟨-b*omegaE,by ring⟩
  have hn : (-3*omegaE:Eisenstein)≠0 :=
    mul_ne_zero (neg_ne_zero.mpr (by norm_num)) (omegaE_primitive.ne_zero (by norm_num))
  change (if (-3*omegaE:Eisenstein)=0 then 1 else
    cubicSymbol (1-3*b*omegaE) (-3*omegaE))=_
  rw [ite_eq_right hn,show (-3*omegaE:Eisenstein)= -(3*omegaE) by ring,
    cubicSymbol_neg hp,cubicSymbol_mul_upper hp,cubicThetaSymbol_three hp,
    show 1-3*b*omegaE=1+3*(-b*omegaE) by ring]
  rfl

lemma cubicTheta_omega_zpow_add_three (a b : ℤ) : omega^(a+3*b)=omega^a := by
  rw [zpow_add₀ (omega_primitive.ne_zero (by norm_num)),zpow_mul]
  have h3 : omega^(3:ℤ)=1 := by norm_num [omega_cube]
  rw [h3,one_zpow,mul_one]

lemma cubicThetaCuspCharacter_coordinates (a b : ℤ) :
    cubicThetaCuspCharacter ((a:Eisenstein)+b*omegaE)=
      cubicThetaUnitCharacter.mulShift (b:Eisenstein) := by
  apply cubicThetaAddChar_eq_of_generators
  · rw [cubicThetaCuspCharacter_one]
    have hn : -((a:Eisenstein)+b*omegaE)=(((-a:ℤ):Eisenstein)+((-b:ℤ):Eisenstein)*omegaE) := by push_cast; ring
    rw [hn,cubicThetaRamifiedCharacter_coordinates]
    change (omega^(2*(-b)))^2=cubicThetaUnitCharacter ((b:Eisenstein)*1)
    have hU : cubicThetaUnitCharacter (b:Eisenstein)=omega^(2*b) := by
      simpa only [Int.cast_zero,zero_mul,add_zero,add_zero] using
        cubicThetaUnitCharacter_coordinates b 0
    rw [mul_one,hU]
    rw [←zpow_natCast (omega^(2*(-b))) 2,←zpow_mul]
    convert cubicTheta_omega_zpow_add_three (2*b) (-2*b) using 1
    congr 1
    ring
  · rw [cubicThetaCuspCharacter_omega]
    have hn : -((a:Eisenstein)+b*omegaE)*omegaE=
        (b:Eisenstein)+((b-a:ℤ):Eisenstein)*omegaE := by
      push_cast
      linear_combination -(b:Eisenstein)*omegaE_quadratic
    rw [hn,cubicThetaRamifiedCharacter_coordinates,cubicThetaUnitCharacter_coordinates]
    change (omega^(2*(b-a)))^2*omega^(2*(b+(b-a)))=
      cubicThetaUnitCharacter ((b:Eisenstein)*omegaE)
    have hU : cubicThetaUnitCharacter ((b:Eisenstein)*omegaE)=omega^(2*b) := by
      simpa only [Int.cast_zero,zero_add,zero_add] using
        cubicThetaUnitCharacter_coordinates 0 b
    rw [hU]
    rw [←zpow_natCast (omega^(2*(b-a))) 2,←zpow_mul,
      ←zpow_add₀ (omega_primitive.ne_zero (by norm_num))]
    convert cubicTheta_omega_zpow_add_three (2*b) (2*b-2*a) using 1
    congr 1
    ring

theorem cubicThetaCuspStepValue_fourier (a b : ℤ) (m : Eisenstein) :
    cubicThetaCuspStepValue ((a:Eisenstein)+b*omegaE) m=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (lambdaE*((b:Eisenstein)*m))) := by
  change cubicThetaCuspCharacter ((a:Eisenstein)+b*omegaE) m=_
  rw [cubicThetaCuspCharacter_coordinates]
  exact cubicThetaUnitCharacter_fourier _

end CubicFirstMoment

end

end OAI
