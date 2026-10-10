import Mathlib
import OAI.Computability.QuantumFactoring.RationalPowerCircuit
import OAI.Computability.QuantumFactoring.EmissionLists
import OAI.Computability.QuantumFactoring.ArithmeticSyntaxEmission
import OAI.Computability.QuantumFactoring.BitStackPowers

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type} (ev : v→List Bool)
lemma exprCode_length (a : NatExpr v) :
    (exprCode ev a).length=2*a.size+2*a.maxConst.bits.length+(listCode (exprTokenCode ev) (exprTokens a)).length+2:=by
  simp only [exprCode,exprPayload,exprView,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
lemma exprCode_const (a : ℕ) : (exprCode ev (NatExpr.const a)).length=4*a.bits.length+11:=by
  rw [exprCode_length]
  simp only [NatExpr.size,NatExpr.maxConst,exprTokens,listCode_length_cons,exprTokenCode,sumCode,List.length_cons]
  have hz : (listCode (sumCode ev (sumCode Nat.bits Nat.bits)) []).length=1:=rfl
  rw [hz];omega
lemma exprCode_mul_le (a b : NatExpr v) :
    (exprCode ev (.mul a b)).length≤(exprCode ev a).length+(exprCode ev b).length+24:=by
  have hm : (max a.maxConst b.maxConst).bits.length≤a.maxConst.bits.length+b.maxConst.bits.length:=by
    rcases le_total a.maxConst b.maxConst with h|h
    · rw [max_eq_right h];omega
    · rw [max_eq_left h];omega
  have h1:=listCode_length_append (exprTokenCode ev) (exprTokens a) (exprTokens b)
  have h2:=listCode_length_append (exprTokenCode ev) (exprTokens a++exprTokens b) [pairToken]
  have h3:=listCode_length_append (exprTokenCode ev) (exprTokens a++exprTokens b++[pairToken]) [opToken 1,compToken]
  rw [exprCode_length,exprCode_length,exprCode_length]
  simp only [NatExpr.size,NatExpr.maxConst,exprTokens]
  have hx : (listCode (exprTokenCode ev) [pairToken]).length=7:=rfl
  have hy : (listCode (exprTokenCode ev) [opToken 1,compToken]).length=19:=rfl
  rw [hx] at h2;rw [hy] at h3
  omega

def exprPowerStep (s : NatExpr v×NatExpr v) : NatExpr v×NatExpr v:=(s.1,.mul s.2 s.1)
lemma exprPowerStep_fst (s : NatExpr v×NatExpr v) (i : ℕ) : ((exprPowerStep^[i]) s).1=s.1:=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply'];exact ih
lemma exprPowerStep_bound (s : NatExpr v×NatExpr v) (i : ℕ) :
    (exprCode ev ((exprPowerStep^[i]) s).2).length≤(exprCode ev s.2).length+i*((exprCode ev s.1).length+24):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    have hh:=exprCode_mul_le ev ((exprPowerStep^[i]) s).2 ((exprPowerStep^[i]) s).1
    rw [exprPowerStep_fst] at hh
    change (exprCode ev (.mul _ _)).length≤_
    rw [exprPowerStep_fst]
    nlinarith
lemma exprPowerStep_start (a : NatExpr v) (i : ℕ) :
    (exprPowerStep^[i]) (a,.const 1)=(a,a.pow i):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',ih];rfl
namespace Emission
noncomputable def exprPowerP : Procedure (prodCode unaryCode (exprCode ev)) (exprCode ev)
    (fun x=>x.2.pow x.1):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let step : Procedure (prodCode (exprCode ev) (exprCode ev)) (prodCode (exprCode ev) (exprCode ev)) exprPowerStep:=
    a.pair ((exprMulP ev).comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 25*Polynomial.X) (by
    intro n s i hi
    have hh:=exprPowerStep_bound ev s i
    simp only [prodCode,pairBits_length,exprPowerStep_fst,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    nlinarith)
  let e:=first unaryCode (exprCode ev)
  let a:=second unaryCode (exprCode ev)
  exact ((second (exprCode ev) (exprCode ev)).comp
    (rep.comp (e.pair (a.pair (Procedure.constant _ (exprCode ev) (.const 1)))))).congrFun (by
      intro x;change ((exprPowerStep^[x.1]) (x.2,.const 1)).2=_
      rw [exprPowerStep_start])
end Emission
namespace Emits
open BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma npow {a : α→NatExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (exprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (exprCode ev) (fun x=>(a x).pow (k x)):=
  (ofProcedure (Emission.exprPowerP ev)).comp (hk.pair ha)
lemma iSignedPower {a : α→IntExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (intExprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (intExprCode ev) (fun x=>(a x).signedPower (k x)):=by
  have hM:=iOfNat (npow (iNatAbs ha) hk)
  exact ((hk.unaryNat.natEven).conditional hM (iIte (ineg ha) (ipos ha) hM (iNeg hM))).congr (by
    intro x;simp only [IntExpr.signedPower,decide_eq_true_eq])
lemma rSignedPower {a : α→RatExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (ratExprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(a x).signedPower (k x)):=
  rmk (iSignedPower (rnum ha) hk) (npow (rden ha) hk)
lemma repeatedSuccess {a : α→RatExpr v} {k : α→ℕ} (ha : BitStackProgram.Emits ea (ratExprCode ev) a)
    (hk : BitStackProgram.Emits ea unaryCode k) : BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(a x).repeatedSuccess (k x)):=
  rSub (const _ _ (RatExpr.const 1)) (rSignedPower (rSub (const _ _ (RatExpr.const 1)) ha) hk)
end Emits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
