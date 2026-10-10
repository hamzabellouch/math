import Mathlib
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma bits_length_pow (a k : ℕ) : (a^k).bits.length≤k*a.bits.length+1:=by
  induction k with
  | zero=>simp
  | succ k ih=>
    have h:=bits_length_mul (a^k) a
    rw [pow_succ];nlinarith

def powerStep (s : ℕ×ℕ) : ℕ×ℕ:=(s.1,s.2*s.1)
lemma powerStep_iterate (s : ℕ×ℕ) (i : ℕ) : (powerStep^[i]) s=(s.1,s.2*s.1^i):=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp [powerStep,pow_succ,Nat.mul_assoc]
namespace Procedure
noncomputable def binaryPow : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x=>x.2^x.1):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let step : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) powerStep:=
    a.pair (binaryMul.comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 3*Polynomial.X+1) (by
    intro n s i hi
    rw [powerStep_iterate]
    have hm:=bits_length_mul s.2 (s.1^i)
    have hp:=bits_length_pow s.1 i
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    nlinarith)
  let e:=first unaryCode Nat.bits
  let x:=second unaryCode Nat.bits
  exact ((second Nat.bits Nat.bits).comp (rep.comp (e.pair (x.pair (constant _ Nat.bits 1))))).congrFun (by
    intro x;change ((powerStep^[x.1]) (x.2,1)).2=x.2^x.1
    rw [powerStep_iterate];simp)
end Procedure
namespace Emits
variable {α : Type} {ea : α→List Bool}
lemma natPow {f k : α→ℕ} (hf : Emits ea Nat.bits f) (hk : Emits ea unaryCode k) :
    Emits ea Nat.bits (fun x=>(f x)^(k x)):=(ofProcedure Procedure.binaryPow).comp (hk.pair hf)
lemma natEven {f : α→ℕ} (hf : Emits ea Nat.bits f) : Emits ea Procedure.boolCode (fun x=>decide (Even (f x))):=by
  have h:=(ofProcedure Procedure.binaryEq).comp ((hf.natMod (const _ _ 2)).pair (const _ _ 0))
  exact h.congr (by intro x;simp only [Nat.even_iff])
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
