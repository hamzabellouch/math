import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.TargetLCExpr

namespace OAI

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open TargetRead TargetRepair
open scoped Classical BigOperators
noncomputable section
variable (u : ℕ)

def edgesExpr : Expr := Expr.power (.mul clausesExpr (.const 3)) u
def countExpr : Expr := .add (.const 3) (.mul (.const 3) (edgesExpr u))
def valueExpr : Expr :=
  let x := Expr.quotient (.sub (.arg 0) (.const 3)) (.const 3)
  let j := Expr.remainder (.sub (.arg 0) (.const 3)) (.const 3)
  Expr.cond (Expr.equal (.arg 0) (.const 0)) (Expr.power clausesExpr u)
    (Expr.cond (Expr.equal (.arg 0) (.const 1)) (Expr.power varsExpr u)
      (Expr.cond (Expr.equal (.arg 0) (.const 2)) (edgesExpr u)
        (Expr.cond (Expr.lt x (edgesExpr u))
          (Expr.cond (Expr.equal j (.const 0)) (leftExpr u x)
            (Expr.cond (Expr.equal j (.const 1)) (rightExpr u x) (projectExpr u x))) (.const 0))))

@[simp] lemma edgesExpr_eval (F : Input) (a : ℕ → ℕ) :
    (edgesExpr u).eval (Complexity.formulaBits F.val) a=(table u F).ne := by
  simp only [edgesExpr,Expr.power_eval,Expr.eval,clausesExpr_eval]
  rfl
@[simp] lemma countExpr_eval (F : Input) (a : ℕ → ℕ) :
    (countExpr u).eval (Complexity.formulaBits F.val) a=3+3*(table u F).ne := by
  simp only [countExpr,Expr.eval,edgesExpr_eval]

lemma valueExpr_eval (F : Input) (w : ℕ) :
    (valueExpr u).eval (Complexity.formulaBits F.val) (fun _ => w)=(table u F).value w := by
  let x := Expr.quotient (.sub (.arg 0) (.const 3)) (.const 3)
  have hx : x.eval (Complexity.formulaBits F.val) (fun _ => w)=(w-3)/3 := by
    simp [x,Expr.quotient_eval,Expr.eval]
  simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,Expr.power_eval,
    clausesExpr_eval,varsExpr_eval,edgesExpr_eval,Table.value]
  by_cases h0 : w=0
  · simp only [h0]; rfl
  by_cases h1 : w=1
  · simp only [h1]; rfl
  by_cases h2 : w=2
  · simp [h2]
  simp only [h0,h1,h2]
  simp only [Expr.lt_eval,Expr.quotient_eval,Expr.remainder_eval,Expr.eval,edgesExpr_eval,indicator_ne]
  by_cases he : (w-3)/3 < (table u F).ne
  · simp only [he,ite_eq_left,dite_eq_left]
    have hl := leftExpr_eval u F x (fun _ => w) ⟨(w-3)/3,he⟩ hx
    have hr := rightExpr_eval u F x (fun _ => w) ⟨(w-3)/3,he⟩ hx
    have hp := projectExpr_eval u F x (fun _ => w) ⟨(w-3)/3,he⟩ hx
    rw [hl,hr,hp]
    rfl
  · simp only [he]
    rfl

lemma serializer_spec (F : Input) :
    UnaryTables.words (fun w => (valueExpr u).eval (Complexity.formulaBits F.val) (fun _ => w))
      ((countExpr u).eval (Complexity.formulaBits F.val) (fun _ => 0))=(table u F).bits := by
  rw [countExpr_eval,Table.bits]
  exact UnaryTables.words_congr (fun w _ => valueExpr_eval u F w)

def certificate : Turing.TM2ComputableInPolyTime (fun F : Input => Complexity.formulaBits F.val)
    Table.bits (table u) :=
  UnaryTables.encodedComputer _ _ _ (countExpr u) (valueExpr u) (serializer_spec u)

lemma finiteAlphabet (k : (certificate u).tm.K) : Finite ((certificate u).tm.Γ k) :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _ k

end
end LargeIndependentSets.TargetLC

end OAI
