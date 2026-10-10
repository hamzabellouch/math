import Mathlib
import OAI.Computability.QuantumFactoring.RationalExpressions
import OAI.Computability.QuantumFactoring.BitStackIntegers
import OAI.Computability.QuantumFactoring.EmissionCombinators

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
def intExprView (a : IntExpr v):=(a.pos,a.neg)
def intExprCode (ev : v→List Bool) (a : IntExpr v):=prodCode (exprCode ev) (exprCode ev) (intExprView a)
def ratExprView (a : RatExpr v):=(a.num,a.den)
def ratExprCode (ev : v→List Bool) (a : RatExpr v):=prodCode (intExprCode ev) (exprCode ev) (ratExprView a)
namespace Emission
noncomputable def intToNatP : Procedure intCode Nat.bits Int.toNat:=
  (conditional intSign (Procedure.constant intCode Nat.bits 0) intAbs).congrFun (by
    intro z;cases z <;> simp)
noncomputable def intExprViewP (ev : v→List Bool) : Procedure (intExprCode ev)
    (prodCode (exprCode ev) (exprCode ev)) intExprView :=(identity _).precompose _
noncomputable def intExprPosP (ev : v→List Bool) : Procedure (intExprCode ev) (exprCode ev) IntExpr.pos:=
  (first _ _).comp (intExprViewP ev)
noncomputable def intExprNegP (ev : v→List Bool) : Procedure (intExprCode ev) (exprCode ev) IntExpr.neg:=
  (second _ _).comp (intExprViewP ev)
noncomputable def intExprMkP (ev : v→List Bool) : Procedure
    (prodCode (exprCode ev) (exprCode ev)) (intExprCode ev) (fun x=>IntExpr.mk x.1 x.2):=
  (identity _).result (by intro x;rfl)
noncomputable def ratExprViewP (ev : v→List Bool) : Procedure (ratExprCode ev)
    (prodCode (intExprCode ev) (exprCode ev)) ratExprView :=(identity _).precompose _
noncomputable def ratExprNumP (ev : v→List Bool) : Procedure (ratExprCode ev) (intExprCode ev) RatExpr.num:=
  (first _ _).comp (ratExprViewP ev)
noncomputable def ratExprDenP (ev : v→List Bool) : Procedure (ratExprCode ev) (exprCode ev) RatExpr.den:=
  (second _ _).comp (ratExprViewP ev)
noncomputable def ratExprMkP (ev : v→List Bool) : Procedure
    (prodCode (intExprCode ev) (exprCode ev)) (ratExprCode ev) (fun x=>RatExpr.mk x.1 x.2):=
  (identity _).result (by intro x;rfl)
end Emission
namespace Emits
variable {α : Type} {ea : α→List Bool} {ev : v→List Bool}
lemma ipos {f : α→IntExpr v} (h : BitStackProgram.Emits ea (intExprCode ev) f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>(f x).pos):=(ofProcedure (Emission.intExprPosP ev)).comp h
lemma ineg {f : α→IntExpr v} (h : BitStackProgram.Emits ea (intExprCode ev) f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>(f x).neg):=(ofProcedure (Emission.intExprNegP ev)).comp h
lemma imk {f g : α→NatExpr v} (h : BitStackProgram.Emits ea (exprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (intExprCode ev) (fun x=>IntExpr.mk (f x) (g x)):=
  (ofProcedure (Emission.intExprMkP ev)).comp (h.pair j)
lemma rnum {f : α→RatExpr v} (h : BitStackProgram.Emits ea (ratExprCode ev) f) :
    BitStackProgram.Emits ea (intExprCode ev) (fun x=>(f x).num):=(ofProcedure (Emission.ratExprNumP ev)).comp h
lemma rden {f : α→RatExpr v} (h : BitStackProgram.Emits ea (ratExprCode ev) f) :
    BitStackProgram.Emits ea (exprCode ev) (fun x=>(f x).den):=(ofProcedure (Emission.ratExprDenP ev)).comp h
lemma rmk {f : α→IntExpr v} {g : α→NatExpr v} (h : BitStackProgram.Emits ea (intExprCode ev) f)
    (j : BitStackProgram.Emits ea (exprCode ev) g) :
    BitStackProgram.Emits ea (ratExprCode ev) (fun x=>RatExpr.mk (f x) (g x)):=
  (ofProcedure (Emission.ratExprMkP ev)).comp (h.pair j)
end Emits
end ExactQuantumFactoring.NetworkEmission

namespace ExactQuantumFactoring
syntax "expr_emit" : tactic
macro_rules
  | `(tactic| expr_emit) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact BitStackProgram.Emits.id _
    | exact BitStackProgram.Emits.const _ _ _
    | (apply NetworkEmission.Emits.ipos; expr_emit)
    | (apply NetworkEmission.Emits.ineg; expr_emit)
    | (apply NetworkEmission.Emits.rnum; expr_emit)
    | (apply NetworkEmission.Emits.rden; expr_emit)
    | (apply NetworkEmission.Emits.imk <;> expr_emit)
    | (apply NetworkEmission.Emits.rmk <;> expr_emit)
    | (apply NetworkEmission.Emits.nvar; expr_emit)
    | (apply NetworkEmission.Emits.nconst; expr_emit)
    | (apply NetworkEmission.Emits.nadd <;> expr_emit)
    | (apply NetworkEmission.Emits.nsub <;> expr_emit)
    | (apply NetworkEmission.Emits.nmul <;> expr_emit)
    | (apply NetworkEmission.Emits.ndiv <;> expr_emit)
    | (apply NetworkEmission.Emits.nmod <;> expr_emit)
    | (apply NetworkEmission.Emits.nite <;> expr_emit)
    | (apply BitStackProgram.Emits.fst; expr_emit)
    | (apply BitStackProgram.Emits.snd; expr_emit)
    | (apply BitStackProgram.Emits.pair <;> expr_emit)
    | (apply BitStackProgram.Emits.natAdd <;> expr_emit)
    | (apply BitStackProgram.Emits.natSub <;> expr_emit)
    | (apply BitStackProgram.Emits.natMul <;> expr_emit)
    | (apply BitStackProgram.Emits.natDiv <;> expr_emit)
    | (apply BitStackProgram.Emits.natMod <;> expr_emit)
    | (apply BitStackProgram.Emits.natMax <;> expr_emit))
end ExactQuantumFactoring

end



end OAI
