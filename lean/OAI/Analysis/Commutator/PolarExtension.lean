import Mathlib
import OAI.Analysis.Commutator.PolarSupport

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positive_kills_of_compression {D P : H →L[ℂ] H} (hD : 0≤D)
    (hP : IsSelfAdjoint P) (h : P*D*P=0) : D*P=0 := by
  have hs : star (CFC.sqrt D*P)*(CFC.sqrt D*P)=0 := by
    rw [star_mul,hP.star_eq,(CFC.sqrt_nonneg D).star_eq]
    calc
      _=P*(CFC.sqrt D*CFC.sqrt D)*P := by noncomm_ring
      _=0 := by rw [CFC.sqrt_mul_sqrt_self D hD,h]
  have hz := (CStarRing.star_mul_self_eq_zero_iff _).mp hs
  calc
    _=(CFC.sqrt D*CFC.sqrt D)*P := by rw [CFC.sqrt_mul_sqrt_self D hD]
    _=0 := by rw [mul_assoc,hz,mul_zero]

lemma abs_fixes_of_square_fixes {W P : H →L[ℂ] H}
    (h : (star W*W)*P=P) : CFC.abs W*P=P := by
  let A := CFC.abs W
  have hA : 0≤A := CFC.abs_nonneg W
  have hu : IsUnit (A+1) := (IsStrictlyPositive.nonneg_add hA isStrictlyPositive_one).isUnit
  have hsq : A*A=star W*W := CFC.abs_mul_abs W
  have he : (A+1)*(A*P-P)=0 := by
    calc
      _=(A*A)*P-P := by noncomm_ring
      _=0 := by rw [hsq,h,sub_self]
  have hz : A*P-P=0 := by
    exact hu.mul_left_cancel (by simpa using he : (A+1)*(A*P-P)=(A+1)*0)
  exact sub_eq_zero.mp hz

lemma partialIsometry_extends {W V : H →L[ℂ] H} (hW : ‖W‖≤1)
    (hV : V*star V*V=V) (hext : W*(star V*V)=V) :
    partialIsometry W*(star V*V)=V ∧ star V*V≤rightSupport W := by
  let P := star V*V
  have hP : IsStarProjection P := by
    constructor
    · change (star V*V)*(star V*V)=star V*V
      calc
        _=star V*(V*star V*V) := by noncomm_ring
        _=star V*V := by rw [hV]
    · exact IsSelfAdjoint.star_mul_self V
  have hwpos : 0≤1-star W*W := by
    apply sub_nonneg.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg W)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg W]
  have hcomp : P*(1-star W*W)*P=0 := by
    have hextstar : P*star W=star V := by
      simpa only [star_mul,star_star] using congrArg star hext
    calc
      _=P*P-(P*star W)*(W*P) := by noncomm_ring
      _=0 := by rw [hP.isIdempotentElem.eq,hextstar,hext]; exact sub_self P
  have hz := positive_kills_of_compression hwpos hP.isSelfAdjoint hcomp
  have hsq : (star W*W)*P=P := by
    rw [sub_mul,one_mul,sub_eq_zero] at hz
    exact hz.symm
  have hAP : CFC.abs W*P=P := abs_fixes_of_square_fixes hsq
  constructor
  · change partialIsometry W*P=V
    calc
      _=partialIsometry W*(CFC.abs W*P) := by rw [hAP]
      _=V := by rw [←mul_assoc,factorization,hext]
  · apply (hP.le_iff_mul_eq_right (isProjection_rightSupport W)).mpr
    change rightSupport W*P=P
    calc
      _=rightSupport W*(CFC.abs W*P) := by rw [hAP]
      _=P := by rw [←mul_assoc,initial_mul_abs,hAP]

end Kadison.Polar

end

end
end

end OAI
