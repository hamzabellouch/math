import Mathlib
import OAI.Computability.QuantumFactoring.RationalExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
def sum (f : ℕ → RatExpr v) : ℕ → RatExpr v
  | 0 => const 0
  | n+1 => add (sum f n) (f n)
@[simp] lemma eval_sum (x : v → ℕ) (f : ℕ → RatExpr v) (n : ℕ) :
    (sum f n).eval x=∑ i ∈ Finset.range n, (f i).eval x := by
  induction n with
  | zero => simp [sum]
  | succ n ih => simp [sum,ih,Finset.sum_range_succ]
end RatExpr

/-- Bounded polynomial arithmetic is itself finite rational syntax. -/
inductive PolyExpr (v : Type*) where
  | C : RatExpr v → PolyExpr v
  | X : PolyExpr v
  | add : PolyExpr v → PolyExpr v → PolyExpr v
  | negation : PolyExpr v → PolyExpr v
  | mul : PolyExpr v → PolyExpr v → PolyExpr v

namespace PolyExpr
variable {v : Type*}
open Polynomial
noncomputable def eval (x : v → ℕ) : PolyExpr v → ℚ[X]
  | .C c => Polynomial.C (c.eval x)
  | .X => Polynomial.X
  | .add a b => a.eval x+b.eval x
  | .negation a => -a.eval x
  | .mul a b => a.eval x*b.eval x

def coeff : PolyExpr v → ℕ → RatExpr v
  | .C c,k => if k=0 then c else RatExpr.const 0
  | .X,k => if k=1 then RatExpr.const 1 else RatExpr.const 0
  | .add a b,k => RatExpr.add (a.coeff k) (b.coeff k)
  | .negation a,k => (a.coeff k).negation
  | .mul a b,k => RatExpr.sum (fun i => RatExpr.mul (a.coeff i) (b.coeff (k-i))) (k+1)

lemma coeff_correct (x : v → ℕ) (p : PolyExpr v) (k : ℕ) :
    (p.coeff k).eval x=(p.eval x).coeff k := by
  induction p generalizing k with
  | C c =>
    by_cases h : k=0 <;> simp [coeff,eval,Polynomial.coeff_C,h]
  | X =>
    by_cases h : k=1 <;> simp [coeff,eval,Polynomial.coeff_X,h,eq_comm]
  | add a b ia ib => simp [coeff,eval,ia,ib]
  | negation a ia => simp [coeff,eval,ia]
  | mul a b ia ib =>
    simp only [coeff,RatExpr.eval_sum,RatExpr.eval_mul,ia,ib,eval,Polynomial.coeff_mul]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (a.eval x).coeff i*(b.eval x).coeff j) k).symm

def sub (a b : PolyExpr v) : PolyExpr v := add a b.negation
def const (r : ℚ) : PolyExpr v := .C (RatExpr.const r)
def pow (a : PolyExpr v) : ℕ → PolyExpr v
  | 0 => const 1
  | n+1 => mul (pow a n) a

def comp : PolyExpr v → PolyExpr v → PolyExpr v
  | .C c,_ => .C c
  | .X,b => b
  | .add a c,b => .add (comp a b) (comp c b)
  | .negation a,b => .negation (comp a b)
  | .mul a c,b => .mul (comp a b) (comp c b)

@[simp] lemma eval_const (x : v → ℕ) (r : ℚ) : (const r : PolyExpr v).eval x=Polynomial.C r := by
  simp [const,eval]
@[simp] lemma eval_sub (x : v → ℕ) (a b : PolyExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,eval,sub_eq_add_neg]
@[simp] lemma eval_pow (x : v → ℕ) (a : PolyExpr v) (n : ℕ) : (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,eval,ih,pow_succ]
@[simp] lemma eval_comp (x : v → ℕ) (a b : PolyExpr v) : (comp a b).eval x=(a.eval x).comp (b.eval x) := by
  induction a with
  | C c => simp [comp,eval]
  | X => simp [comp,eval]
  | add a c ia ic => simp [comp,eval,ia,ic,Polynomial.add_comp]
  | negation a ia => simp [comp,eval,ia,Polynomial.neg_comp]
  | mul a c ia ic => simp [comp,eval,ia,ic,Polynomial.mul_comp]
end PolyExpr
end ExactQuantumFactoring


end

end OAI
