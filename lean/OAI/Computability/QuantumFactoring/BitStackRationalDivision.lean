import Mathlib
import OAI.Computability.QuantumFactoring.BitStackRationals

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def ratInv : Procedure ratCode ratCode (fun q=>q⁻¹):=by
  let num:=signedInt.comp ((intSign.comp ratNum).pair ratDen)
  let den:=intAbs.comp ratNum
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro q
    change mkRat (intOfSign (decide (q.num<0),q.den)) q.num.natAbs=q⁻¹
    rw [Rat.mkRat_eq_div]
    by_cases h:q.num<0
    · have hz:=Int.eq_neg_natAbs_of_nonpos h.le
      simp only [h,decide_true,intOfSign,ite_true,Int.cast_neg,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,hz]
      simp only [Int.cast_neg,Int.cast_natCast,neg_div,inv_neg,inv_div]
    · have hz:=Int.natAbs_of_nonneg (le_of_not_gt h)
      simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,←hz]
      simp only [inv_div,Int.cast_natCast])
noncomputable def ratDiv : Procedure (prodCode ratCode ratCode) ratCode (fun x=>x.1/x.2):=
  (ratMul.comp ((first ratCode ratCode).pair (ratInv.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (div_eq_mul_inv _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
