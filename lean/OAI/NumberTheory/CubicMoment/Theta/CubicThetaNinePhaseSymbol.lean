import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNinePhase
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitCharacterFourier

namespace OAI

/-! The modulus-nine phase in the actual ramified residue is the
supplementary cubic character in the arithmetic theta formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNinePhase_coordinates (a b : ℤ) :
    cubicThetaNinePhase (ofCoords a b)=(Real.fourierChar ((b:ℝ)/9):ℂ) := by
  have hd : dualRealCoords ![0,(1/9:ℝ)]=1/(9*traceLambda) := by
    rw [dualRealCoords_eq]
    norm_num
    ring
  have hc : (ofCoords a b:ℂ)=eisensteinRealCoords ![(a:ℝ),(b:ℝ)] := by
    simp [eisensteinRealCoords_apply,ofCoords_coe]
  rw [cubicThetaNinePhase,residueFourierChar_mk]
  congr 2
  change tracePair (ofCoords a b:ℂ) (1/(9*traceLambda))=_
  rw [hc,←hd,dualRealCoords_trace]
  simp [Fin.sum_univ_two]
  ring

lemma cubicThetaNinePhase_one : cubicThetaNinePhase 1=1 := by
  have h := cubicThetaNinePhase_coordinates 1 0
  have he : ofCoords 1 0=(1:Eisenstein) := by
    apply Subtype.ext
    simp [ofCoords_coe]
  simpa only [he,Int.cast_zero,zero_div,AddChar.map_zero_eq_one,Circle.coe_one] using h

lemma cubicThetaNinePhase_three (t : Eisenstein) :
    cubicThetaNinePhase (3*t)=
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) t) := by
  unfold cubicThetaNinePhase
  simpa only [mul_one] using cubicThetaFourier_nine_triple t 1

lemma cubicThetaNinePhase_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaNinePhase h=cubicSymbol h (lambdaE^2) := by
  obtain ⟨t,ht⟩ := hh
  have he : h=1+3*t := by linear_combination ht
  have hp : primary (1+3*t) := ⟨t,by ring⟩
  rw [he,cubicThetaNinePhase_add,cubicThetaNinePhase_one,one_mul,
    cubicThetaNinePhase_three,cubicSymbol_pow_upper hp]
  change residueFourierChar 3 _ (Ideal.Quotient.mk (modulus 3) t)=
    (cubicThetaRamifiedCharacter t)^2
  rw [cubicThetaRamifiedCharacter_fourier,pow_two,←AddChar.map_add_eq_mul,←map_add]
  apply congrArg (residueFourierChar 3 (by norm_num))
  apply residue_eq_of_dvd_sub
  exact ⟨-t,by ring⟩

end CubicFirstMoment

end

end OAI
