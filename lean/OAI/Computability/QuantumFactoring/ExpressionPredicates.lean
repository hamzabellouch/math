import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionTemplateCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

def testEq (a b : NatExpr v) (yes no : NatExpr v) : NatExpr v :=
  .iteLe a b (.iteLe b a yes no) no
lemma eval_testEq (x : v → ℕ) (a b yes no : NatExpr v) :
    (testEq a b yes no).eval x=if a.eval x=b.eval x then yes.eval x else no.eval x := by
  simp only [testEq,eval]
  split_ifs <;> omega

/-- A total exact predicate compiler. All intermediate words are widened from
an explicit expression-derived bound, including on rejected inputs. -/
def isOne {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  equalOn (e.template vars) (wordConstant (BitVec.ofNat (e.templateWidth b) 1))
lemma isOne_eval {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) (x : Basis k) :
    (e.isOne vars).eval x 0=true ↔ e.eval (fun i => (bitsValue ((vars i).eval x)).toNat)=1 := by
  rw [isOne,equalOn_value,template_value,wordConstant_eval,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  apply Nat.one_lt_two_pow
  have hh := Nat.mul_pos (show 0<b+e.maxConst.size+1 by omega) e.size_pos
  exact hh.ne'
lemma isOne_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.isOne vars).net.count ≤
      e.cost*(operationBound (e.templateWidth b)+c+e.templateWidth b)+
        100*(e.templateWidth b)+21 := by
  have he := e.template_count vars hc
  have hh := equalOn_count (e.template vars) (wordConstant (n:=k) (BitVec.ofNat (e.templateWidth b) 1))
  simp only [wordConstant_count] at hh
  exact hh.trans (by omega)
end NatExpr
end ExactQuantumFactoring


end

end OAI
