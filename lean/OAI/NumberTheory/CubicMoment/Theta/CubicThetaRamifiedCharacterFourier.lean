import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCharacter

namespace OAI

/-! The exact additive frequency of the ramified supplementary character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedCharacter_trace (a b : ℤ) :
    tracePair (ofCoords a b:ℂ) ((2:ℂ)/(3*traceLambda))=(2*(b:ℝ))/3 := by
  have hd : dualRealCoords ![0,(2/3:ℝ)]=(2:ℂ)/(3*traceLambda) := by
    rw [dualRealCoords_eq]
    norm_num
    ring
  have hc : (ofCoords a b:ℂ)=eisensteinRealCoords ![(a:ℝ),(b:ℝ)] := by
    simp [eisensteinRealCoords_apply,ofCoords_coe]
  rw [hc,← hd,dualRealCoords_trace]
  simp [Fin.sum_univ_two]
  ring

theorem cubicThetaRamifiedCharacter_fourier (t : Eisenstein) :
    cubicThetaRamifiedCharacter t=
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (2*t)) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective t
  change cubicThetaRamifiedCharacter (ofCoords a b)=
    residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (2*ofCoords a b))
  rw [show ofCoords a b=(a:Eisenstein)+b*omegaE from rfl,
    cubicThetaRamifiedCharacter_coordinates]
  rw [residueFourierChar_mk]
  have ht : tracePair (((2:Eisenstein)*((a:Eisenstein)+b*omegaE):Eisenstein):ℂ)
      (1/((3:Eisenstein):ℂ)/traceLambda)=(2*(b:ℝ))/3 := by
    have hc := cubicThetaRamifiedCharacter_trace a b
    convert hc using 1
    unfold tracePair
    congr 2
    rw [ofCoords_coe]
    push_cast
    change (2:ℂ)*((a:ℂ)+(b:ℂ)*omega)*(1/3/traceLambda)=
      ((a:ℂ)+(b:ℂ)*omega)*(2/(3*traceLambda))
    ring
  have hs : (1:ℂ)/(((3:Eisenstein):ℂ)*traceLambda)=
      1/((3:Eisenstein):ℂ)/traceLambda := by ring
  rw [hs,ht]
  have hw : (Real.fourierChar (1/3:ℝ):ℂ)=omega := by
    rw [Real.fourierChar_apply]
    unfold omega
    congr 1
    push_cast
    ring
  have hw2 : (Real.fourierChar (2/3:ℝ):ℂ)=omega^2 := by
    rw [show (2/3:ℝ)=1/3+1/3 by ring,AddChar.map_add_eq_mul,Circle.coe_mul,hw]
    ring
  rw [show 2*(b:ℝ)/3=b • (2/3:ℝ) by simp; ring,
    AddChar.map_zsmul_eq_zpow,Circle.coe_zpow,hw2,
    ← zpow_natCast omega 2,← zpow_mul]
  norm_num

end CubicFirstMoment

end

end OAI
