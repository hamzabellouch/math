import Mathlib
import OAI.Computability.QuantumFactoring.RationalExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

def ifLe (a b c d : IntExpr v) : IntExpr v :=
  iteLe (.add a.pos b.neg) (.add b.pos a.neg) c d
@[simp] lemma eval_ifLe (x : v → ℕ) (a b c d : IntExpr v) :
    (ifLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  simp only [ifLe,eval_iteLe,NatExpr.eval]
  have he : a.pos.eval x+b.neg.eval x ≤ b.pos.eval x+a.neg.eval x ↔ a.eval x ≤ b.eval x := by
    simp only [eval]
    omega
  simp only [he]
end IntExpr

namespace RatExpr
variable {v : Type*}

def ifNatLe (a b : NatExpr v) (c d : RatExpr v) : RatExpr v :=
  ⟨IntExpr.iteLe a b c.num d.num,.iteLe a b c.den d.den⟩
@[simp] lemma eval_ifNatLe (x : v → ℕ) (a b : NatExpr v) (c d : RatExpr v) :
    (ifNatLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  by_cases h : a.eval x ≤ b.eval x
  · simp [ifNatLe,eval,NatExpr.eval,h]
  · simp [ifNatLe,eval,NatExpr.eval,h]

def ifIntLe (a b : IntExpr v) (c d : RatExpr v) : RatExpr v :=
  ifNatLe (.add a.pos b.neg) (.add b.pos a.neg) c d
@[simp] lemma eval_ifIntLe (x : v → ℕ) (a b : IntExpr v) (c d : RatExpr v) :
    (ifIntLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  rw [ifIntLe,eval_ifNatLe]
  simp only [NatExpr.eval]
  have hh : a.pos.eval x+b.neg.eval x ≤ b.pos.eval x+a.neg.eval x ↔ a.eval x ≤ b.eval x := by
    simp only [IntExpr.eval]
    omega
  simp only [hh]

def ifLe (a b c d : RatExpr v) : RatExpr v :=
  let a := a.normalize
  let b := b.normalize
  ifIntLe (a.num.scale b.den) (b.num.scale a.den) c d
@[simp] lemma eval_ifLe (x : v → ℕ) (a b c d : RatExpr v) :
    (ifLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  rw [ifLe,eval_ifIntLe]
  simp only [IntExpr.eval_scale]
  have ha : (0 : ℚ) < a.normalize.den.eval x := by exact_mod_cast normalize_den_pos x a
  have hb : (0 : ℚ) < b.normalize.den.eval x := by exact_mod_cast normalize_den_pos x b
  have he : a.normalize.num.eval x * b.normalize.den.eval x ≤
      b.normalize.num.eval x * a.normalize.den.eval x ↔ a.eval x ≤ b.eval x := by
    rw [← eval_normalize x a,← eval_normalize x b,eval,eval,div_le_div_iff₀ ha hb]
    norm_cast
  simp only [he]

def ifLt (a b c d : RatExpr v) : RatExpr v := ifLe b a d c
def ifEq (a b c d : RatExpr v) : RatExpr v := ifLe a b (ifLe b a c d) d
def max (a b : RatExpr v) : RatExpr v := ifLe a b b a
def min (a b : RatExpr v) : RatExpr v := ifLe a b a b
@[simp] lemma eval_ifLt (x : v → ℕ) (a b c d : RatExpr v) :
    (ifLt a b c d).eval x = if a.eval x < b.eval x then c.eval x else d.eval x := by
  simp only [ifLt,eval_ifLe]
  by_cases h : a.eval x < b.eval x
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]
@[simp] lemma eval_ifEq (x : v → ℕ) (a b c d : RatExpr v) :
    (ifEq a b c d).eval x = if a.eval x = b.eval x then c.eval x else d.eval x := by
  simp only [ifEq,eval_ifLe]
  by_cases h : a.eval x = b.eval x
  · simp [h]
  · by_cases h₁ : a.eval x ≤ b.eval x
    · have h₂ : ¬b.eval x ≤ a.eval x := fun hh => h (le_antisymm h₁ hh)
      simp [h,h₁,h₂]
    · simp [h,h₁]
@[simp] lemma eval_max (x : v → ℕ) (a b : RatExpr v) : (max a b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp [max,_root_.max_def]
@[simp] lemma eval_min (x : v → ℕ) (a b : RatExpr v) : (min a b).eval x=Min.min (a.eval x) (b.eval x) := by
  simp [min,_root_.min_def]
end RatExpr
end ExactQuantumFactoring


end

end OAI
