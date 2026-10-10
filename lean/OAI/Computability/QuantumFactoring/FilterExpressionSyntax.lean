import Mathlib
import OAI.Computability.QuantumFactoring.PolynomialExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
instance (n : ℕ) : OfNat (RatExpr v) n := ⟨const n⟩
instance : Add (RatExpr v) := ⟨add⟩
instance : Mul (RatExpr v) := ⟨mul⟩
instance : Sub (RatExpr v) := ⟨sub⟩
instance : Div (RatExpr v) := ⟨div⟩
instance : Neg (RatExpr v) := ⟨negation⟩
instance : Inv (RatExpr v) := ⟨inverse⟩
instance : Pow (RatExpr v) ℕ := ⟨pow⟩
@[simp] lemma eval_num (x : v → ℕ) (n : ℕ) : (no_index (OfNat.ofNat n : RatExpr v)).eval x=n := eval_const x n
@[simp] lemma eval_plus (x : v → ℕ) (a b : RatExpr v) : (a+b).eval x=a.eval x+b.eval x := eval_add x a b
@[simp] lemma eval_times (x : v → ℕ) (a b : RatExpr v) : (a*b).eval x=a.eval x*b.eval x := eval_mul x a b
@[simp] lemma eval_minus (x : v → ℕ) (a b : RatExpr v) : (a-b).eval x=a.eval x-b.eval x := eval_sub x a b
@[simp] lemma eval_over (x : v → ℕ) (a b : RatExpr v) : (a/b).eval x=a.eval x/b.eval x := eval_div x a b
@[simp] lemma eval_neg (x : v → ℕ) (a : RatExpr v) : (-a).eval x= -a.eval x := eval_negation x a
@[simp] lemma eval_inv (x : v → ℕ) (a : RatExpr v) : (a⁻¹).eval x=(a.eval x)⁻¹ := eval_inverse x a
@[simp] lemma eval_power (x : v → ℕ) (a : RatExpr v) (n : ℕ) : (a^n).eval x=(a.eval x)^n := eval_pow x a n
end RatExpr
namespace PolyExpr
variable {v : Type*}
instance (n : ℕ) : OfNat (PolyExpr v) n := ⟨const n⟩
instance : Add (PolyExpr v) := ⟨add⟩
instance : Mul (PolyExpr v) := ⟨mul⟩
instance : Sub (PolyExpr v) := ⟨sub⟩
instance : Neg (PolyExpr v) := ⟨negation⟩
instance : Pow (PolyExpr v) ℕ := ⟨pow⟩
@[simp] lemma eval_num (x : v → ℕ) (n : ℕ) : (no_index (OfNat.ofNat n : PolyExpr v)).eval x=Polynomial.C (n : ℚ) := eval_const x n
@[simp] lemma eval_plus (x : v → ℕ) (a b : PolyExpr v) : (a+b).eval x=a.eval x+b.eval x := rfl
@[simp] lemma eval_times (x : v → ℕ) (a b : PolyExpr v) : (a*b).eval x=a.eval x*b.eval x := rfl
@[simp] lemma eval_minus (x : v → ℕ) (a b : PolyExpr v) : (a-b).eval x=a.eval x-b.eval x := eval_sub x a b
@[simp] lemma eval_neg (x : v → ℕ) (a : PolyExpr v) : (-a).eval x= -a.eval x := rfl
@[simp] lemma eval_power (x : v → ℕ) (a : PolyExpr v) (n : ℕ) : (a^n).eval x=(a.eval x)^n := eval_pow x a n
end PolyExpr
end ExactQuantumFactoring


end

end OAI
