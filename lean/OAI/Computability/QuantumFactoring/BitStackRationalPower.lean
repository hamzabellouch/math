import Mathlib
import OAI.Computability.QuantumFactoring.BitStackRationals
import OAI.Computability.QuantumFactoring.BitStackOptions
import OAI.Computability.QuantumFactoring.BitStackPowers

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma intOfSign_pow (z : ℤ) (k : ℕ) :
    intOfSign (decide (z<0) && decide (k%2=1),z.natAbs^k)=z^k:=by
  by_cases hz:z<0
  · have he:=Int.eq_neg_natAbs_of_nonpos hz.le
    conv_rhs=>rw [he,neg_pow,neg_one_pow_eq_pow_mod_two]
    have hk:=Nat.mod_lt k (by omega : 0<2)
    have hp:k%2=0 ∨ k%2=1:=by omega
    rcases hp with h|h <;> simp [intOfSign,hz,h]
  · have he:=Int.natAbs_of_nonneg (le_of_not_gt hz)
    simp only [hz,decide_false,Bool.false_and,intOfSign,Bool.false_eq_true,ite_false,Int.natCast_pow,he]
namespace Procedure
noncomputable def intPow : Procedure (prodCode unaryCode intCode) intCode (fun x=>x.2^x.1):=by
  let k:=first unaryCode intCode
  let z:=second unaryCode intCode
  let odd:=binaryEq.comp ((binaryMod.comp ((unaryToBits.comp k).pair
    (constant _ Nat.bits 2))).pair (constant _ Nat.bits 1))
  let s:=boolAnd.comp ((intSign.comp z).pair odd)
  let a:=binaryPow.comp (k.pair (intAbs.comp z))
  exact (signedInt.comp (s.pair a)).congrFun (by intro x;exact intOfSign_pow x.2 x.1)
noncomputable def ratPow : Procedure (prodCode unaryCode ratCode) ratCode (fun x=>x.2^x.1):=by
  let k:=first unaryCode ratCode
  let q:=second unaryCode ratCode
  let num:=intPow.comp (k.pair (ratNum.comp q))
  let den:=binaryPow.comp (k.pair (ratDen.comp q))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.2.num^x.1) (x.2.den^x.1)=x.2^x.1
    rw [Rat.mkRat_eq_div,Int.cast_pow,Nat.cast_pow,←div_pow,Rat.num_div_den])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
