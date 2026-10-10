import Mathlib
import OAI.Computability.QuantumFactoring.IntegerExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Rational arithmetic as fixed finite syntax over nonnegative registers. No
canonical-fraction reduction or unit-cost large-integer operation is required. -/
structure RatExpr (v : Type*) where
  num : IntExpr v
  den : NatExpr v

namespace RatExpr
variable {v : Type*}

def eval (x : v → ℕ) (a : RatExpr v) : ℚ := (a.num.eval x : ℚ)/(a.den.eval x : ℚ)
def ofNat (a : NatExpr v) : RatExpr v := ⟨IntExpr.ofNat a,.const 1⟩
def ofInt (a : IntExpr v) : RatExpr v := ⟨a,.const 1⟩
def const (a : ℚ) : RatExpr v := ⟨IntExpr.ofInt a.num,.const a.den⟩
def normalize (a : RatExpr v) : RatExpr v :=
  ⟨IntExpr.iteLe a.den (.const 0) (IntExpr.ofInt 0) a.num,
   .iteLe a.den (.const 0) (.const 1) a.den⟩
def add (a b : RatExpr v) : RatExpr v :=
  let a := normalize a
  let b := normalize b
  ⟨IntExpr.add (a.num.scale b.den) (b.num.scale a.den),.mul a.den b.den⟩
def negation (a : RatExpr v) : RatExpr v := ⟨a.num.negation,a.den⟩
def sub (a b : RatExpr v) : RatExpr v := add a b.negation
def mul (a b : RatExpr v) : RatExpr v := ⟨a.num.mul b.num,.mul a.den b.den⟩
def inverse (a : RatExpr v) : RatExpr v :=
  ⟨a.num.scale a.den,.mul a.num.natAbs a.num.natAbs⟩
def div (a b : RatExpr v) : RatExpr v := mul a b.inverse
def pow (a : RatExpr v) : ℕ → RatExpr v
  | 0 => const 1
  | n+1 => mul (pow a n) a

@[simp] lemma eval_ofNat (x : v → ℕ) (a : NatExpr v) : (ofNat a).eval x=a.eval x := by
  simp [ofNat,eval,NatExpr.eval]
@[simp] lemma eval_ofInt (x : v → ℕ) (a : IntExpr v) : (ofInt a).eval x=a.eval x := by
  simp [ofInt,eval,NatExpr.eval]
@[simp] lemma eval_const (x : v → ℕ) (a : ℚ) : (const a : RatExpr v).eval x=a := by
  simp [const,eval,NatExpr.eval,Rat.num_div_den]
@[simp] lemma eval_normalize (x : v → ℕ) (a : RatExpr v) : a.normalize.eval x=a.eval x := by
  by_cases h : a.den.eval x=0
  · simp [normalize,eval,NatExpr.eval,h]
  · have hp : ¬a.den.eval x ≤ 0 := by omega
    simp [normalize,eval,NatExpr.eval,hp]
lemma normalize_den_pos (x : v → ℕ) (a : RatExpr v) : 0 < a.normalize.den.eval x := by
  change 0 < if a.den.eval x ≤ 0 then 1 else a.den.eval x
  split_ifs <;> omega
@[simp] lemma eval_add (x : v → ℕ) (a b : RatExpr v) : (add a b).eval x=a.eval x+b.eval x := by
  have ha : (a.normalize.den.eval x : ℚ) ≠ 0 := by exact_mod_cast (normalize_den_pos x a).ne'
  have hb : (b.normalize.den.eval x : ℚ) ≠ 0 := by exact_mod_cast (normalize_den_pos x b).ne'
  rw [← eval_normalize x a,← eval_normalize x b]
  simp only [add,eval,IntExpr.eval_add,IntExpr.eval_scale,NatExpr.eval,Int.cast_add,
    Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp
@[simp] lemma eval_negation (x : v → ℕ) (a : RatExpr v) : a.negation.eval x= -a.eval x := by
  simp [negation,eval,neg_div]
@[simp] lemma eval_sub (x : v → ℕ) (a b : RatExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,sub_eq_add_neg]
@[simp] lemma eval_mul (x : v → ℕ) (a b : RatExpr v) : (mul a b).eval x=a.eval x*b.eval x := by
  simp [mul,eval,NatExpr.eval,div_mul_div_comm]
@[simp] lemma eval_inverse (x : v → ℕ) (a : RatExpr v) : a.inverse.eval x=(a.eval x)⁻¹ := by
  simp only [inverse,eval,IntExpr.eval_scale,IntExpr.eval_natAbs,NatExpr.eval,
    Int.cast_mul,Int.cast_natCast,Nat.cast_mul,inv_div]
  have hsq : ((a.num.eval x).natAbs : ℚ)*((a.num.eval x).natAbs : ℚ) =
      (a.num.eval x : ℚ)*(a.num.eval x : ℚ) := by
    rw [← sq,← sq]
    have h : ((a.num.eval x).natAbs : ℤ)^2=(a.num.eval x)^2 := by
      rw [Int.natCast_natAbs,sq_abs]
    simpa only [Int.cast_pow,Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) h
  rw [hsq]
  by_cases hz : (a.num.eval x : ℚ)=0
  · simp [hz]
  · field_simp
@[simp] lemma eval_div (x : v → ℕ) (a b : RatExpr v) : (div a b).eval x=a.eval x/b.eval x := by
  simp [div,div_eq_mul_inv]
@[simp] lemma eval_pow (x : v → ℕ) (a : RatExpr v) (n : ℕ) : (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,ih,pow_succ]

end RatExpr
end ExactQuantumFactoring


end

end OAI
