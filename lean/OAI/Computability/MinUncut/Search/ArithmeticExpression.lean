import Mathlib
import OAI.Computability.MinUncut.Estimates.IterationMagnitude

namespace OAI

section
namespace MinUncut.Costed
inductive AExpr where
  | const (n : ℕ)
  | reg (i : ℕ)
  | add (a b : AExpr)
  | sub (a b : AExpr)
  | mul (a b : AExpr)
  | div (a b : AExpr)
  | mod (a b : AExpr)
  | eq (a b : AExpr)
  | le (a b : AExpr)
  | at (a : AExpr)
  | cond (e a b : AExpr)

def AExpr.eval : AExpr → List ℕ → ℕ
  | .const n,_ => n
  | .reg i,v => (v.drop i).headI
  | .add a b,v => a.eval v+b.eval v
  | .sub a b,v => a.eval v-b.eval v
  | .mul a b,v => a.eval v*b.eval v
  | .div a b,v => a.eval v/b.eval v
  | .mod a b,v => a.eval v%b.eval v
  | .eq a b,v => if a.eval v=b.eval v then 1 else 0
  | .le a b,v => if a.eval v≤b.eval v then 1 else 0
  | .at a,v => (v.drop (a.eval v)).headI
  | .cond e a b,v => if e.eval v=0 then a.eval v else b.eval v

noncomputable def AExpr.program : (a : AExpr) → PolyProgram (fun v=>[a.eval v])
  | .const n => PolyProgram.const n
  | .reg i => PolyProgram.projection i
  | .add a b => PolyProgram.addOf a.program b.program
  | .sub a b => PolyProgram.subOf a.program b.program
  | .mul a b => PolyProgram.mulOf a.program b.program
  | .div a b => Division.quotient.comp (a.program.cons (b.program.cons PolyProgram.nil))
  | .mod a b => Division.remainder.comp (a.program.cons (b.program.cons PolyProgram.nil))
  | .eq a b => PolyProgram.eqOf a.program b.program
  | .le a b => PolyProgram.leOf a.program b.program
  | .at a => PolyProgram.dynamic.comp (a.program.cons PolyProgram.id)
  | .cond e a b => (PolyProgram.branch e.program a.program b.program).ofEq (by
      intro v
      change (if e.eval v=0 then [a.eval v] else [b.eval v])=[if e.eval v=0 then a.eval v else b.eval v]
      split_ifs <;> rfl)

def AExpr.pow (a : AExpr) : ℕ → AExpr
  | 0 => .const 1
  | n+1 => .mul (a.pow n) a
lemma AExpr.eval_pow (a : AExpr) (n : ℕ) (v : List ℕ) : (a.pow n).eval v=a.eval v^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow,eval,ih,pow_succ]

def AExpr.sum : List AExpr → AExpr
  | [] => .const 0
  | a::as => .add a (sum as)
lemma AExpr.eval_sum (as : List AExpr) (v : List ℕ) : (sum as).eval v=(as.map (fun a=>a.eval v)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [sum,eval,List.map_cons,List.sum_cons,ih]

def AExpr.lookup (a : AExpr) : List (ℕ × ℕ) → AExpr
  | [] => .const 0
  | (i,x)::xs => .cond (.eq a (.const i)) (a.lookup xs) (.const x)
def AExpr.lookupValue (n : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (i,x)::xs => if n=i then x else lookupValue n xs
lemma AExpr.eval_lookup (a : AExpr) (xs : List (ℕ × ℕ)) (v : List ℕ) :
    (a.lookup xs).eval v=lookupValue (a.eval v) xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨i,x⟩
    by_cases h : a.eval v=i <;> simp only [lookup,eval,lookupValue,h,ite_true,ite_false,
      Nat.one_ne_zero,ih]

end MinUncut.Costed

end

end OAI
