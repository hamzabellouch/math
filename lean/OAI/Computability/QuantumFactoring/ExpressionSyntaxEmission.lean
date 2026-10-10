import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionTemplateCircuit
import OAI.Computability.QuantumFactoring.Procedure
import OAI.Computability.QuantumFactoring.ExpressionPostfix
import OAI.Computability.QuantumFactoring.BitStackSumInjection

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type}
def exprView (e : NatExpr v) := (e.size,e.maxConst,exprTokens e)
def exprPayload (ev : v→List Bool):=prodCode unaryCode (prodCode Nat.bits (listCode (exprTokenCode ev)))
def exprCode (ev : v→List Bool) (e : NatExpr v):=exprPayload ev (exprView e)
namespace Emission
variable (ev : v→List Bool)
noncomputable def exprViewP : Procedure (exprCode ev) (exprPayload ev) exprView:=
  (identity (exprPayload ev)).precompose exprView
noncomputable def exprSizeP : Procedure (exprCode ev) unaryCode NatExpr.size:=
  (first unaryCode _).comp (exprViewP ev)
noncomputable def exprMaxP : Procedure (exprCode ev) Nat.bits NatExpr.maxConst:=
  (first Nat.bits _).comp ((second unaryCode _).comp (exprViewP ev))
noncomputable def exprTokensP : Procedure (exprCode ev) (listCode (exprTokenCode ev)) exprTokens:=
  (second Nat.bits _).comp ((second unaryCode _).comp (exprViewP ev))
noncomputable def binaryMax : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>max x.1 x.2):=
  (conditional binaryLe (second Nat.bits Nat.bits) (first Nat.bits Nat.bits)).congrFun (by
    intro x;simp only [decide_eq_true_eq];split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (by omega)).symm)
noncomputable def exprVarP : Procedure ev (exprCode ev) NatExpr.var:=by
  let token:=(sumLeft ev (sumCode Nat.bits Nat.bits))
  let ts:=(listCons (exprTokenCode ev)).comp (token.pair (Procedure.constant ev (listCode (exprTokenCode ev)) []))
  exact ((Procedure.constant ev unaryCode 1).pair ((Procedure.constant ev Nat.bits 0).pair ts)).result (by intro i;rfl)
noncomputable def constTokenP : Procedure Nat.bits (exprTokenCode ev) (fun c=>Sum.inr (Sum.inl c)):=
  (sumRight ev (sumCode Nat.bits Nat.bits)).comp (sumLeft Nat.bits Nat.bits)
noncomputable def exprConstP : Procedure Nat.bits (exprCode ev) NatExpr.const:=by
  let ts:=(listCons (exprTokenCode ev)).comp ((constTokenP ev).pair (Procedure.constant Nat.bits (listCode (exprTokenCode ev)) []))
  exact ((Procedure.constant Nat.bits unaryCode 1).pair ((identity Nat.bits).pair ts)).result (by intro i;rfl)
noncomputable def tokensAppendP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>x.1++x.2):=listAppend _ (opToken 0)
noncomputable def tokensPairP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>x.1++x.2++[pairToken]):=
  (tokensAppendP ev).comp ((tokensAppendP ev).pair (Procedure.constant _ _ [pairToken]))
noncomputable def tokensOpP (j : ℕ) : Procedure (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))
    (fun ts=>ts++[opToken j,compToken]):=
  (tokensAppendP ev).comp ((identity _).pair (Procedure.constant _ _ [opToken j,compToken]))
noncomputable def tokensLeP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>leTokens x.1 x.2):=
  (tokensOpP ev 6).comp ((tokensOpP ev 5).comp ((tokensPairP ev).comp
    ((second _ _).pair (first _ _))))
noncomputable def tokensMuxP : Procedure (prodCode (listCode (exprTokenCode ev))
    (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))))
    (listCode (exprTokenCode ev)) (fun x=>muxTokens x.1 x.2.1 x.2.2):=by
  let a:=first (listCode (exprTokenCode ev)) (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
  let rs:=second (listCode (exprTokenCode ev)) (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
  let b:=(first (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))).comp rs
  let c:=(second (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))).comp rs
  exact (tokensOpP ev 7).comp ((tokensPairP ev).comp (((tokensPairP ev).comp (a.pair b)).pair c))
noncomputable def exprBinaryP (j : ℕ) (f : NatExpr v→NatExpr v→NatExpr v)
    (hs : ∀a b,(f a b).size=a.size+b.size+1)
    (hm : ∀a b,(f a b).maxConst=max a.maxConst b.maxConst)
    (ht : ∀a b,exprTokens (f a b)=exprTokens a++exprTokens b++[pairToken]++[opToken j,compToken]) :
    Procedure (prodCode (exprCode ev) (exprCode ev)) (exprCode ev) (fun x=>f x.1 x.2):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let sz:=unarySuccessor.comp (unaryAdd.comp (((exprSizeP ev).comp a).pair ((exprSizeP ev).comp b)))
  let mx:=binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))
  let ts:=(tokensOpP ev j).comp ((tokensPairP ev).comp (((exprTokensP ev).comp a).pair ((exprTokensP ev).comp b)))
  exact (sz.pair (mx.pair ts)).result (by intro x;simp only [exprCode,exprView,hs,hm,ht];rfl)
noncomputable def exprAddP:=exprBinaryP ev 0 NatExpr.add (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprMulP:=exprBinaryP ev 1 NatExpr.mul (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprDivP:=exprBinaryP ev 3 NatExpr.div (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprModP:=exprBinaryP ev 4 NatExpr.mod (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprSubP : Procedure (prodCode (exprCode ev) (exprCode ev)) (exprCode ev) (fun x=>NatExpr.sub x.1 x.2):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let sz:=unarySuccessor.comp (unaryAdd.comp (((exprSizeP ev).comp a).pair ((exprSizeP ev).comp b)))
  let mx:=binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))
  let as':=(exprTokensP ev).comp a
  let bs:=(exprTokensP ev).comp b
  let test:=(tokensLeP ev).comp (bs.pair as')
  let sub:=(tokensOpP ev 2).comp ((tokensPairP ev).comp (as'.pair bs))
  let z:=Procedure.constant (prodCode (exprCode ev) (exprCode ev)) (listCode (exprTokenCode ev)) [.inr (.inl 0)]
  exact (sz.pair (mx.pair ((tokensMuxP ev).comp (test.pair (sub.pair z))))).result (by intro x;rfl)
noncomputable def exprIteP : Procedure (prodCode (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev))))
    (exprCode ev) (fun x=>NatExpr.iteLe x.1 x.2.1 x.2.2.1 x.2.2.2):=by
  let a:=first (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev)))
  let rs:=second (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev)))
  let b:=(first (exprCode ev) (prodCode (exprCode ev) (exprCode ev))).comp rs
  let rt:=(second (exprCode ev) (prodCode (exprCode ev) (exprCode ev))).comp rs
  let c:=(first (exprCode ev) (exprCode ev)).comp rt
  let d:=(second (exprCode ev) (exprCode ev)).comp rt
  let sz:=unarySuccessor.comp (unaryAdd.comp ((unaryAdd.comp ((unaryAdd.comp (((exprSizeP ev).comp a).pair
    ((exprSizeP ev).comp b))).pair ((exprSizeP ev).comp c))).pair ((exprSizeP ev).comp d)))
  let mx:=binaryMax.comp ((binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))).pair
    (binaryMax.comp (((exprMaxP ev).comp c).pair ((exprMaxP ev).comp d))))
  let test:=(tokensLeP ev).comp (((exprTokensP ev).comp a).pair ((exprTokensP ev).comp b))
  let ts:=(tokensMuxP ev).comp (test.pair (((exprTokensP ev).comp c).pair ((exprTokensP ev).comp d)))
  exact (sz.pair (mx.pair ts)).result (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
