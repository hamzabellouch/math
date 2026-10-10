import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitCharacter

namespace OAI

/-! The finite additive frequency of the unit supplementary character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAddChar_eq_of_generators (φ ψ : AddChar Eisenstein ℂ)
    (h1 : φ 1=ψ 1) (hω : φ omegaE=ψ omegaE) : φ=ψ := by
  ext t
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective t
  change φ ((a:Eisenstein)+b*omegaE)=ψ ((a:Eisenstein)+b*omegaE)
  rw [AddChar.map_add_eq_mul,AddChar.map_add_eq_mul]
  have ha : (a:Eisenstein)=a • (1:Eisenstein) := by simp
  have hb : (b:Eisenstein)*omegaE=b • omegaE := by simp
  rw [ha,hb,AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,
    AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,h1,hω]

def cubicThetaUnitFourierCharacter : AddChar Eisenstein ℂ :=
  ((residueFourierChar 3 (by norm_num)).mulShift
    (Ideal.Quotient.mk (modulus 3) lambdaE)).compAddMonoidHom
      (Ideal.Quotient.mk (modulus 3)).toAddMonoidHom

lemma cubicThetaUnitFourierCharacter_apply (t : Eisenstein) :
    cubicThetaUnitFourierCharacter t=
      (Real.fourierChar (tracePair (t:ℂ) (1/3)):ℂ) := by
  change residueFourierChar 3 (by norm_num)
    (Ideal.Quotient.mk (modulus 3) lambdaE*Ideal.Quotient.mk (modulus 3) t)=_
  rw [← map_mul,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  rw [lambdaE_coe]
  change (traceLambda*(t:ℂ))*(1/(3*traceLambda))=(t:ℂ)*(1/3)
  field_simp [traceLambda_ne_zero]

theorem cubicThetaUnitCharacter_fourier (t : Eisenstein) :
    cubicThetaUnitCharacter t=
      residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (lambdaE*t)) := by
  have hw : (Real.fourierChar (1/3:ℝ):ℂ)=omega := by
    rw [Real.fourierChar_apply]
    unfold omega
    congr 1
    push_cast
    ring
  have he : cubicThetaUnitCharacter=cubicThetaUnitFourierCharacter := by
    apply cubicThetaAddChar_eq_of_generators
    · rw [cubicThetaUnitCharacter_one,cubicThetaUnitFourierCharacter_apply]
      have ht : tracePair ((1:Eisenstein):ℂ) (1/3)=(1/3:ℝ)+(1/3:ℝ) := by
        norm_num [tracePair]
      rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul,hw]
      ring
    · rw [cubicThetaUnitCharacter_omega,cubicThetaUnitFourierCharacter_apply]
      have ht : tracePair (omegaE:ℂ) (1/3)=-(1/3:ℝ) := by
        change 2*(omega*(1/3:ℂ)).re=-(1/3:ℝ)
        norm_num [Complex.mul_re,omega_re]
      rw [ht,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,hw]
      exact star_omega.symm
  rw [he]
  change residueFourierChar 3 (by norm_num)
    (Ideal.Quotient.mk (modulus 3) lambdaE*Ideal.Quotient.mk (modulus 3) t)=_
  rw [← map_mul]

end CubicFirstMoment

end

end OAI
