import Mathlib
import OAI.Computability.QuantumFactoring.NaturalExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Balanced integers avoid a word-size-dependent signed representation. -/
structure IntExpr (v : Type*) where
  pos : NatExpr v
  neg : NatExpr v

namespace IntExpr
variable {v : Type*}

def eval (x : v → ℕ) (e : IntExpr v) : ℤ := (e.pos.eval x : ℤ)-e.neg.eval x

def ofNat (e : NatExpr v) : IntExpr v := ⟨e,.const 0⟩
def ofInt (z : ℤ) : IntExpr v := ⟨.const z.toNat,.const (-z).toNat⟩
def add (a b : IntExpr v) : IntExpr v := ⟨.add a.pos b.pos,.add a.neg b.neg⟩
def negation (a : IntExpr v) : IntExpr v := ⟨a.neg,a.pos⟩
def sub (a b : IntExpr v) : IntExpr v := add a (negation b)
def mul (a b : IntExpr v) : IntExpr v :=
  ⟨.add (.mul a.pos b.pos) (.mul a.neg b.neg),
   .add (.mul a.neg b.pos) (.mul a.pos b.neg)⟩
def scale (a : IntExpr v) (b : NatExpr v) : IntExpr v := mul a (ofNat b)
def toNat (a : IntExpr v) : NatExpr v := .sub a.pos a.neg
def natAbs (a : IntExpr v) : NatExpr v := .add (.sub a.pos a.neg) (.sub a.neg a.pos)
def iteLe (a b : NatExpr v) (c d : IntExpr v) : IntExpr v :=
  ⟨.iteLe a b c.pos d.pos,.iteLe a b c.neg d.neg⟩

@[simp] lemma eval_ofNat (x : v → ℕ) (e : NatExpr v) : (ofNat e).eval x=(e.eval x : ℤ) := by
  simp [ofNat,eval,NatExpr.eval]
@[simp] lemma eval_ofInt (x : v → ℕ) (z : ℤ) : (ofInt z : IntExpr v).eval x=z := by
  simp [ofInt,eval,NatExpr.eval]
@[simp] lemma eval_add (x : v → ℕ) (a b : IntExpr v) : (add a b).eval x=a.eval x+b.eval x := by
  simp [add,eval,NatExpr.eval]
  ring
@[simp] lemma eval_negation (x : v → ℕ) (a : IntExpr v) : (negation a).eval x= -a.eval x := by
  simp [negation,eval]
@[simp] lemma eval_sub (x : v → ℕ) (a b : IntExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,sub_eq_add_neg]
@[simp] lemma eval_mul (x : v → ℕ) (a b : IntExpr v) : (mul a b).eval x=a.eval x*b.eval x := by
  simp [mul,eval,NatExpr.eval]
  ring
@[simp] lemma eval_scale (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (scale a b).eval x=a.eval x*b.eval x := by simp [scale]
@[simp] lemma eval_toNat (x : v → ℕ) (a : IntExpr v) : (toNat a).eval x=(a.eval x).toNat := by
  simp [toNat,NatExpr.eval,eval]
@[simp] lemma eval_natAbs (x : v → ℕ) (a : IntExpr v) : (natAbs a).eval x=(a.eval x).natAbs := by
  simp only [natAbs,NatExpr.eval,eval]
  omega
@[simp] lemma eval_iteLe (x : v → ℕ) (a b : NatExpr v) (c d : IntExpr v) :
    (iteLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  simp only [iteLe,eval,NatExpr.eval]
  split_ifs <;> rfl

end IntExpr
end ExactQuantumFactoring


end

end OAI
