import Mathlib
import OAI.Computability.QuantumFactoring.BitStackPowers
import OAI.Computability.QuantumFactoring.ExpressionPowerEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type} (ev : v→List Bool)
lemma bits_length_max_le (a b : ℕ) : (max a b).bits.length≤a.bits.length+b.bits.length:=by
  rcases le_total a b with h|h
  · rw [max_eq_right h];omega
  · rw [max_eq_left h];omega
lemma tokenCode_length_append (a b : List (ExprToken v)) :
    (listCode (exprTokenCode ev) (a++b)).length=(listCode (exprTokenCode ev) a).length+(listCode (exprTokenCode ev) b).length-1:=by
  have h:=listCode_length_append (exprTokenCode ev) a b;omega
lemma exprCode_ite_le (a b c d : NatExpr v) :
    (exprCode ev (.iteLe a b c d)).length≤(exprCode ev a).length+(exprCode ev b).length+
      (exprCode ev c).length+(exprCode ev d).length+100:=by
  have h1:=bits_length_max_le a.maxConst b.maxConst
  have h2:=bits_length_max_le c.maxConst d.maxConst
  have h3:=bits_length_max_le (max a.maxConst b.maxConst) (max c.maxConst d.maxConst)
  simp only [exprCode_length,NatExpr.size,NatExpr.maxConst,exprTokens,muxTokens,leTokens]
  have hpair : (listCode (exprTokenCode ev) [pairToken]).length=7:=rfl
  have ho5 : (listCode (exprTokenCode ev) [opToken 5,compToken]).length=21:=rfl
  have ho6 : (listCode (exprTokenCode ev) [opToken 6,compToken]).length=23:=rfl
  have ho7 : (listCode (exprTokenCode ev) [opToken 7,compToken]).length=23:=rfl
  simp only [tokenCode_length_append,hpair,ho5,ho6,ho7]
  omega

def coveringStep (s : ℕ×(NatExpr v×NatExpr v)) : ℕ×(NatExpr v×NatExpr v):=
  (s.1*2,s.2.1,.iteLe s.2.1 (.const s.1) s.2.2 (.const (s.1*2)))
lemma coveringStep_pow (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    ((coveringStep^[i]) s).1=s.1*2^i:=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply'];change ((coveringStep^[i]) s).1*2=_
               rw [ih,pow_succ,Nat.mul_assoc]
lemma coveringStep_base (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    ((coveringStep^[i]) s).2.1=s.2.1:=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply'];exact ih
lemma coveringStep_pow_size (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    (((coveringStep^[i]) s).1).bits.length≤(s.1).bits.length+2*i+1:=by
  rw [coveringStep_pow]
  have hm:=bits_length_mul s.1 (2^i)
  have hp:=bits_length_pow 2 i
  have ht : (2:ℕ).bits.length=2:=rfl
  rw [ht] at hp;omega
lemma coveringStep_expr_bound (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    (exprCode ev ((coveringStep^[i]) s).2.2).length≤(exprCode ev s.2.2).length+
      i*((exprCode ev s.2.1).length+8*(s.1).bits.length+16*i+200):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    have hh:=exprCode_ite_le ev ((coveringStep^[i]) s).2.1 (.const ((coveringStep^[i]) s).1)
      ((coveringStep^[i]) s).2.2 (.const (((coveringStep^[i]) s).1*2))
    rw [exprCode_const,exprCode_const,coveringStep_base] at hh
    have hp:=coveringStep_pow_size s i
    have h2:=bits_length_mul ((coveringStep^[i]) s).1 2
    have ht : (2:ℕ).bits.length=2:=rfl
    rw [ht] at h2
    rw [Function.iterate_succ_apply']
    change (exprCode ev (.iteLe _ _ _ _)).length≤_
    rw [coveringStep_base]
    nlinarith
lemma coveringStep_start (d : NatExpr v) (i : ℕ) :
    (coveringStep^[i]) (1,d,.const 1)=(2^i,d,OrderTrial.Expressions.coveringPow d i):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp only [coveringStep,pow_succ,OrderTrial.Expressions.coveringPow]
namespace Emission
noncomputable def coveringPowP : Procedure (prodCode unaryCode (exprCode ev)) (exprCode ev)
    (fun x=>OrderTrial.Expressions.coveringPow x.2 x.1):=by
  let ecode:=prodCode (exprCode ev) (exprCode ev)
  let scode:=prodCode Nat.bits ecode
  let p:=first Nat.bits ecode
  let r:=second Nat.bits ecode
  let d:=(first (exprCode ev) (exprCode ev)).comp r
  let a:=(second (exprCode ev) (exprCode ev)).comp r
  let p2:=binaryMul.comp (p.pair (Procedure.constant scode Nat.bits 2))
  let expr:=(exprIteP ev).comp (d.pair (((exprConstP ev).comp p).pair
    (a.pair ((exprConstP ev).comp p2))))
  let step : Procedure scode scode coveringStep:=p2.pair (d.pair expr)
  let rep:=step.iterate (Polynomial.C 100*Polynomial.X^2+Polynomial.C 205*Polynomial.X+2) (by
    intro n s i hi
    have hp:=coveringStep_pow_size s i
    have he:=coveringStep_expr_bound ev s i
    simp only [scode,ecode,prodCode,pairBits_length,coveringStep_base,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,
      Polynomial.eval_ofNat]
    nlinarith)
  let k:=first unaryCode (exprCode ev)
  let d:=second unaryCode (exprCode ev)
  let start:=(Procedure.constant _ Nat.bits 1).pair (d.pair (Procedure.constant _ (exprCode ev) (.const 1)))
  let out:=(second (exprCode ev) (exprCode ev)).comp (second Nat.bits ecode)
  exact (out.comp (rep.comp (k.pair start))).congrFun (by
    intro x;change ((coveringStep^[x.1]) (1,x.2,.const 1)).2.2=_
    rw [coveringStep_start])
end Emission
namespace Emits
open BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma coveringPow {d : α→NatExpr v} {k : α→ℕ} (hd : BitStackProgram.Emits ea (exprCode ev) d)
    (hk : BitStackProgram.Emits ea unaryCode k) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>OrderTrial.Expressions.coveringPow (d x) (k x)):=
  (ofProcedure (Emission.coveringPowP ev)).comp (hk.pair hd)
end Emits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
