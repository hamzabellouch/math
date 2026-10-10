import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedRowInflation
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedCubicValues

namespace OAI

/-! The supplementary character on primary elements modulo nine is
an additive character of their two integral coordinates. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedCharacter : AddChar Eisenstein ℂ where
  toFun t := cubicSymbol (1+3*t) lambdaE
  map_zero_eq_one' := by simp only [mul_zero,add_zero,cubicSymbol_one_lower]
  map_add_eq_mul' a b := by
    have ha : primary (1+3*a) := ⟨a,by ring⟩
    have hb : primary (1+3*b) := ⟨b,by ring⟩
    have hab : primary (1+3*(a+b)) := ⟨a+b,by ring⟩
    have he := cubicSymbol_lambda_periodic (primary_mul ha hb) hab
      (show (9:Eisenstein) ∣ (1+3*a)*(1+3*b)-(1+3*(a+b)) from ⟨a*b,by ring⟩)
    rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hb)] at he
    exact he.symm

lemma cubicThetaRamifiedCharacter_one : cubicThetaRamifiedCharacter 1=1 := by
  change cubicSymbol (1+3*(1:Eisenstein)) lambdaE=1
  rw [show (1+3*(1:Eisenstein))=(-2)*(-2) by ring,
    cubicSymbol_mul_lower (by norm_num) (by norm_num),cubicSymbol_neg_two_lambda]
  norm_num

lemma cubicThetaRamifiedCharacter_omega : cubicThetaRamifiedCharacter omegaE=omega^2 :=
  cubicSymbol_seven_factor_lambda

theorem cubicThetaRamifiedCharacter_coordinates (a b : ℤ) :
    cubicThetaRamifiedCharacter ((a:Eisenstein)+b*omegaE)=omega^(2*b) := by
  rw [AddChar.map_add_eq_mul]
  have ha : cubicThetaRamifiedCharacter (a:Eisenstein)=1 := by
    rw [show (a:Eisenstein)=a • (1:Eisenstein) by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaRamifiedCharacter_one,one_zpow]
  have hb : cubicThetaRamifiedCharacter ((b:Eisenstein)*omegaE)=(omega^2)^b := by
    rw [show (b:Eisenstein)*omegaE=b • omegaE by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaRamifiedCharacter_omega]
  rw [ha,hb,one_mul]
  rw [← zpow_natCast omega 2,← zpow_mul]
  norm_num

theorem cubicSymbol_lambda_primary_coordinates (a b : ℤ) :
    cubicSymbol (1+3*((a:Eisenstein)+b*omegaE)) lambdaE=omega^(2*b) :=
  cubicThetaRamifiedCharacter_coordinates a b

end CubicFirstMoment

end

end OAI
