import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialDivision

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

inductive Expr where
  | input : ℕ → Expr
  | number : ℕ → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

def Expr.eval : Expr → List ℕ → ℕ
  | .input i, xs => xs.getD i 0
  | .number n, _ => n
  | .plus a b, xs => a.eval xs+b.eval xs
  | .times a b, xs => a.eval xs*b.eval xs

def Expr.realizer : (e : Expr) → Realizer e.eval
  | .input i => composition (pair identity (constant i)) (getDFast 0)
  | .number n => constant n
  | .plus a b => composition (pair a.realizer b.realizer) add
  | .times a b => composition (pair a.realizer b.realizer) multiply

lemma Expr.polynomial (e : Expr) : PolynomialTime e.realizer := by
  induction e with
  | input i => exact polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_constant i)) (polynomial_getDFast 0)
  | number n => exact polynomial_constant n
  | plus a b ha hb => exact polynomial_composition (polynomial_pair ha hb) polynomial_add
  | times a b ha hb => exact polynomial_composition (polynomial_pair ha hb) polynomial_multiply

def Expr.pow (a : Expr) : ℕ → Expr
  | 0 => .number 1
  | n+1 => .times (a.pow n) a

lemma Expr.eval_pow (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a.pow n).eval xs=(a.eval xs)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Expr.pow,Expr.eval,ih,pow_succ]


instance (n : ℕ) : OfNat Expr n := ⟨.number n⟩
instance : Add Expr := ⟨.plus⟩
instance : Mul Expr := ⟨.times⟩
instance : Pow Expr ℕ := ⟨Expr.pow⟩

@[simp] lemma Expr.eval_power (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a^n).eval xs=(a.eval xs)^n := Expr.eval_pow a n xs

@[simp] lemma Expr.eval_add (a b : Expr) (xs : List ℕ) :
    (a+b).eval xs=a.eval xs+b.eval xs := rfl
@[simp] lemma Expr.eval_mul (a b : Expr) (xs : List ℕ) :
    (a*b).eval xs=a.eval xs*b.eval xs := rfl
@[simp] lemma Expr.eval_ofNat (n : ℕ) (xs : List ℕ) :
    (OfNat.ofNat n : Expr).eval xs=n := rfl

def vector (es : List Expr) (xs : List ℕ) : List ℕ := es.map (fun e => e.eval xs)

def vectorRealizer : (es : List Expr) → Realizer (vector es)
  | [] => constant []
  | e::es => composition (pair e.realizer (vectorRealizer es)) listCons

lemma polynomial_vector (es : List Expr) : PolynomialTime (vectorRealizer es) := by
  induction es with
  | nil => exact polynomial_constant []
  | cons e es ih => exact polynomial_composition (polynomial_pair e.polynomial ih) polynomial_listCons


end ContingencyTables.ScalarScheduleProgram

end OAI
