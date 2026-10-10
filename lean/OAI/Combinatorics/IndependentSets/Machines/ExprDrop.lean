import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.Represented

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators

def dropInput (offset : Expr) : Expr → Expr
  | .const n => .const n
  | .arg i => .arg i
  | .length => .sub .length (UnaryTables.closed offset)
  | .bit x => .bit (.add (UnaryTables.closed offset) (dropInput offset x))
  | .add x y => .add (dropInput offset x) (dropInput offset y)
  | .sub x y => .sub (dropInput offset x) (dropInput offset y)
  | .mul x y => .mul (dropInput offset x) (dropInput offset y)
  | .zero x => .zero (dropInput offset x)
  | .sum b f => .sum (dropInput offset b) (dropInput offset f)

lemma dropInput_eval (offset e : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (dropInput offset e).eval s a=e.eval (s.drop (offset.eval s (fun _ => 0))) a := by
  have hc (a : ℕ → ℕ) : (UnaryTables.closed offset).eval s a=offset.eval s (fun _ => 0) := by
    simp [UnaryTables.closed,UnaryTables.atIndex,eval]
  induction e generalizing a with
  | const n => rfl
  | arg n => rfl
  | length => simp [dropInput,eval,hc]
  | bit e ih => simp [dropInput,eval,hc,ih,List.getElem?_drop]
  | add x y ix iy => simp [dropInput,eval,ix,iy]
  | sub x y ix iy => simp [dropInput,eval,ix,iy]
  | mul x y ix iy => simp [dropInput,eval,ix,iy]
  | zero x ix => simp [dropInput,eval,ix]
  | sum b f ib iF => simp only [dropInput,eval,ib,iF]

end IndependentSetsCut.CounterMachine.Expr

namespace IndependentSetsCut.CounterMachine.UnaryTables
lemma words_add (f : ℕ → ℕ) (a b : ℕ) :
    words f (a+b)=words f a ++ words (fun w => f (a+w)) b := by
  induction b with
  | zero => simp [words]
  | succ b ih => rw [Nat.add_succ,words_succ,ih,words_succ,List.append_assoc]
end IndependentSetsCut.CounterMachine.UnaryTables

end OAI
