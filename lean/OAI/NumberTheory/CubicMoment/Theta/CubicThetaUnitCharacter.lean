import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCharacterFourier

namespace OAI

/-! The second finite character needed at the ramified place: the unit
omega, restricted to primary numerators. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaUnitCharacter : AddChar Eisenstein ℂ where
  toFun t := cubicSymbol (1+3*t) omegaE
  map_zero_eq_one' := by simp only [mul_zero,add_zero,cubicSymbol_one_lower]
  map_add_eq_mul' a b := by
    have ha : primary (1+3*a) := ⟨a,by ring⟩
    have hb : primary (1+3*b) := ⟨b,by ring⟩
    have hab : primary (1+3*(a+b)) := ⟨a+b,by ring⟩
    have he := cubicSymbol_omega_periodic (primary_mul ha hb) hab
      (show (9:Eisenstein) ∣ (1+3*a)*(1+3*b)-(1+3*(a+b)) from ⟨a*b,by ring⟩)
    rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hb)] at he
    exact he.symm

lemma cubicThetaUnitCharacter_one : cubicThetaUnitCharacter 1=omega^2 := by
  change cubicSymbol (1+3*(1:Eisenstein)) omegaE=omega^2
  rw [show (1+3*(1:Eisenstein))=(-2)*(-2) by ring,
    cubicSymbol_mul_lower (by norm_num) (by norm_num),cubicSymbol_neg_two_omega]
  ring

lemma cubicThetaUnitCharacter_omega : cubicThetaUnitCharacter omegaE=omega^2 :=
  cubicSymbol_seven_factor_omega

theorem cubicThetaUnitCharacter_coordinates (a b : ℤ) :
    cubicThetaUnitCharacter ((a:Eisenstein)+b*omegaE)=omega^(2*(a+b)) := by
  rw [AddChar.map_add_eq_mul]
  have ha : cubicThetaUnitCharacter (a:Eisenstein)=(omega^2)^a := by
    rw [show (a:Eisenstein)=a • (1:Eisenstein) by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaUnitCharacter_one]
  have hb : cubicThetaUnitCharacter ((b:Eisenstein)*omegaE)=(omega^2)^b := by
    rw [show (b:Eisenstein)*omegaE=b • omegaE by simp,
      AddChar.map_zsmul_eq_zpow,cubicThetaUnitCharacter_omega]
  rw [ha,hb,← zpow_add₀ (pow_ne_zero 2 (omega_primitive.ne_zero (by decide)))]
  rw [← zpow_natCast omega 2,← zpow_mul]
  norm_num

end CubicFirstMoment

end

end OAI
