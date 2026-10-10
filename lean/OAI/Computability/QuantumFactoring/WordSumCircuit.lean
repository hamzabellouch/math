import Mathlib
import OAI.Computability.QuantumFactoring.WordNetworks

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

def sumNet {k w : ℕ} : List (BooleanNetwork k w)→BooleanNetwork k w
  | []=>wordConstant 0
  | a::as=>(a.pair (sumNet as)).comp (add w)

lemma sumNet_nat {k w : ℕ} (as : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((sumNet as).eval x)).toNat=
      (as.map (fun a=>(bitsValue (a.eval x)).toNat)).sum%2^w := by
  induction as with
  | nil=>simp [sumNet,wordConstant_eval]
  | cons a as ih=>
    simp only [sumNet,eval_comp,eval_pair,add_word,BitVec.toNat_add,ih,
      List.map_cons,List.sum_cons,Nat.add_mod_mod]

lemma sumNet_count {k w c : ℕ} (as : List (BooleanNetwork k w))
    (h : ∀ a∈as,a.net.count≤c) :
    (sumNet as).net.count≤as.length*(c+86*w+6)+w := by
  induction as with
  | nil=>simp [sumNet,wordConstant_count]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hi:=ih (fun b hb=>h b (by simp [hb]))
    have hh:=add_count w
    simp only [sumNet,count_comp,count_pair,List.length_cons]
    nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
