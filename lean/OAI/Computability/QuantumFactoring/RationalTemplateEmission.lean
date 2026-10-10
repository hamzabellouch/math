import Mathlib
import OAI.Computability.QuantumFactoring.PolynomialFilterExpressions
import OAI.Computability.QuantumFactoring.ArithmeticSyntaxEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emits
open BitStackProgram BitStackProgram.Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
local notation "NEm" => BitStackProgram.Emits ea (exprCode ev)
local notation "REm" => BitStackProgram.Emits ea (ratExprCode ev)
lemma nMin {a b : α→NatExpr v} (ha : NEm a) (hb : NEm b) : NEm (fun x=>NatExpr.min (a x) (b x)):=nite ha hb ha hb
lemma nMax {a b : α→NatExpr v} (ha : NEm a) (hb : NEm b) : NEm (fun x=>NatExpr.max (a x) (b x)):=nite ha hb hb ha
lemma nPow {a : α→NatExpr v} (ha : NEm a) (k : ℕ) : NEm (fun x=>NatExpr.pow (a x) k):=by
  induction k with
  | zero=>exact const _ _ (NatExpr.const 1)
  | succ k ih=>exact nmul ih ha
lemma rSum {a : α→ℕ→RatExpr v} (ha : ∀i,REm (fun x=>a x i)) (k : ℕ) :
    REm (fun x=>RatExpr.sum (a x) k):=by
  induction k with
  | zero=>exact const _ _ (RatExpr.const 0)
  | succ k ih=>exact rAdd ih (ha k)
lemma rSumList {β : Type} {a : α→β→RatExpr v} (ha : ∀i,REm (fun x=>a x i)) (l : List β) :
    REm (fun x=>RatExpr.sumList (a x) l):=by
  induction l with
  | nil=>exact const _ _ (RatExpr.const 0)
  | cons b bs ih=>exact rAdd (ha b) ih
end ExactQuantumFactoring.NetworkEmission.Emits
namespace ExactQuantumFactoring
syntax "rat_emit" : tactic
macro_rules
  | `(tactic| rat_emit) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact BitStackProgram.Emits.const _ _ _
    | (apply NetworkEmission.Emits.rOfInt;rat_emit)
    | (apply NetworkEmission.Emits.rOfNat;rat_emit)
    | (apply NetworkEmission.Emits.rConst;rat_emit)
    | (apply NetworkEmission.Emits.rIfEq <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfLt <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfLe <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfIntLe <;> rat_emit)
    | (apply NetworkEmission.Emits.rIfNatLe <;> rat_emit)
    | (apply NetworkEmission.Emits.rMax <;> rat_emit)
    | (apply NetworkEmission.Emits.rMin <;> rat_emit)
    | (apply NetworkEmission.Emits.rAdd <;> rat_emit)
    | (apply NetworkEmission.Emits.rSub <;> rat_emit)
    | (apply NetworkEmission.Emits.rMul <;> rat_emit)
    | (apply NetworkEmission.Emits.rDiv <;> rat_emit)
    | (apply NetworkEmission.Emits.rNeg;rat_emit)
    | (apply NetworkEmission.Emits.rInv;rat_emit)
    | (apply NetworkEmission.Emits.rPow;rat_emit)
    | (apply NetworkEmission.Emits.rCeil;rat_emit)
    | (apply NetworkEmission.Emits.rFloor;rat_emit)
    | (apply NetworkEmission.Emits.rCeilNat;rat_emit)
    | (apply NetworkEmission.Emits.nMin <;> rat_emit)
    | (apply NetworkEmission.Emits.nMax <;> rat_emit)
    | (apply NetworkEmission.Emits.nPow;rat_emit)
    | (apply NetworkEmission.Emits.nadd <;> rat_emit)
    | (apply NetworkEmission.Emits.nsub <;> rat_emit)
    | (apply NetworkEmission.Emits.nmul <;> rat_emit)
    | (apply NetworkEmission.Emits.ndiv <;> rat_emit)
    | (apply NetworkEmission.Emits.nmod <;> rat_emit))
end ExactQuantumFactoring

end



end OAI
