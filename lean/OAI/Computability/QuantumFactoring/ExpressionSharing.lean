import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionTemplateCircuit
import OAI.Computability.QuantumFactoring.RetentionExpressions

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

/-- Only truncated subtraction duplicates its operands in the actual compiler.
In particular a priority-search tail in an ite is compiled ONCE, not twice. -/
def sharedCost : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .div a b | .mod a b => a.sharedCost+b.sharedCost+1
  | .sub a b => 2*(a.sharedCost+b.sharedCost)+1
  | .iteLe a b c d => a.sharedCost+b.sharedCost+c.sharedCost+d.sharedCost+1

lemma compile_shared_count {k w c : ℕ} (vars : v → BooleanNetwork k w)
    (hc : ∀ i, (vars i).net.count ≤ c) (e : NatExpr v) :
    (e.compile vars).net.count ≤ e.sharedCost*(operationBound w+c) := by
  induction e with
  | var i => simpa only [compile,sharedCost,one_mul] using (hc i).trans (Nat.le_add_left c _)
  | const d => simp only [compile,sharedCost,one_mul,wordConstant_count,operationBound]; omega
  | add a b ia ib =>
    have hh := add_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | mul a b ia ib =>
    have hh := mul_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | sub a b ia ib =>
    have hh := natSubOn_count (a.compile vars) (b.compile vars)
    change (natSubOn (a.compile vars) (b.compile vars)).net.count ≤ _
    simp only [sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | div a b ia ib =>
    have hh := div_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | mod a b ia ib =>
    have hh := mod_count w
    simp only [compile,count_comp,count_pair,sharedCost]
    dsimp [operationBound] at *
    nlinarith
  | iteLe a b d e ia ib id ie =>
    have hh := wordLe_count (a.compile vars) (b.compile vars)
    simp only [compile,wordMux_count,sharedCost]
    dsimp [operationBound] at *
    nlinarith

lemma template_shared_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.template vars).net.count ≤
      e.sharedCost*(operationBound (e.templateWidth b)+c+e.templateWidth b) := by
  unfold template
  have hh := e.compile_shared_count (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))
    (c:=c+e.templateWidth b) (by
      intro i
      rw [count_comp]
      exact Nat.add_le_add (hc i) (resizeWord_count _ _))
  simpa only [Nat.add_assoc] using hh

end NatExpr
namespace OrderTrial.Expressions
variable {v : Type*}

lemma coveringPow_sharedCost (d : NatExpr v) (n : ℕ) :
    (coveringPow d n).sharedCost=n*(d.sharedCost+3)+1 := by
  induction n with
  | zero => simp [coveringPow,NatExpr.sharedCost]
  | succ n ih => simp only [coveringPow,NatExpr.sharedCost,ih]; ring

lemma coveringPow_size (d : NatExpr v) (n : ℕ) :
    (coveringPow d n).size=n*(d.size+3)+1 := by
  induction n with
  | zero => simp [coveringPow,NatExpr.size]
  | succ n ih => simp only [coveringPow,NatExpr.size,ih]; ring

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
