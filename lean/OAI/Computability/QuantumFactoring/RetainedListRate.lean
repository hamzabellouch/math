import Mathlib
import OAI.Computability.QuantumFactoring.RationalPowerCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion.Expressions

def listRate (n K : ℕ) : RatExpr (Fin 2) :=
  ((RatExpr.ofNat (v:=Fin 2) (.var 1)).div (RatExpr.ofNat (OrderTrial.Expressions.coveringPow (.var 0) n))).repeatedSuccess K

lemma listRate_value (n K m F : ℕ) (hm : m≤2^n) :
    (listRate n K).eval (fun i : Fin 2=>if i=0 then m else F)=
      1-(1-(F:ℚ)/(2:ℚ)^(Nat.clog 2 m))^K := by
  rw [listRate,RatExpr.repeatedSuccess_value,RatExpr.eval_div,RatExpr.eval_ofNat,
    RatExpr.eval_ofNat,OrderTrial.Expressions.coveringPow_correct]
  · simp only [NatExpr.eval,Fin.one_eq_zero_iff,OfNat.ofNat_ne_one,ite_false,ite_true,
      Nat.cast_pow,Nat.cast_ofNat]
  · simpa only [NatExpr.eval,ite_true] using hm
end Completion.Expressions


end ExactQuantumFactoring
end

end OAI
