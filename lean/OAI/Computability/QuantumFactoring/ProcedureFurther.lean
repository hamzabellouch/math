import Mathlib
import OAI.Computability.QuantumFactoring.BitStackDivision
import OAI.Computability.QuantumFactoring.BitStackGCD

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def gcdStepP : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) gcdStep :=
  (conditional (binaryZero.comp (second Nat.bits Nat.bits))
    (identity (prodCode Nat.bits Nat.bits)) ((second Nat.bits Nat.bits).pair binaryMod)).congrFun
      (by intro x;simp only [gcdStep,Function.comp_apply,id_eq,decide_eq_true_eq])

noncomputable def binaryGcd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>x.1.gcd x.2) := by
  let p:=(gcdStepP.comp gcdStepP).congrFun (g:=gcdRound) (by intro x;rfl)
  let rep:=p.iterate (Polynomial.C 2*Polynomial.X+1) (by
    intro n x i _
    have hh:=gcdRound_iterate_sizeSum i x
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let len:=(length.precompose Nat.bits).comp (second Nat.bits Nat.bits)
  exact ((first Nat.bits Nat.bits).comp (rep.comp (len.pair (identity (prodCode Nat.bits Nat.bits))))).congrFun
    (by intro x;exact gcdRound_result x)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
