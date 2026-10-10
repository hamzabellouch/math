import Mathlib
import OAI.Computability.QuantumFactoring.RationalExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

def ceilRatioNat (a : IntExpr v) (b : NatExpr v) : NatExpr v :=
  .div (.sub (.add a.toNat b) (.const 1)) b

def floorRatio (a : IntExpr v) (b : NatExpr v) : IntExpr v :=
  sub (ofNat (.div a.toNat b)) (ofNat (ceilRatioNat a.negation b))

lemma ceil_ratio_nat (z : ℤ) (d : ℕ) :
    (Int.ceil ((z:ℚ)/d)).toNat=(z.toNat+d-1)/d := by
  by_cases hd : d=0
  · simp [hd]
  have hd' : (0:ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  apply eq_of_forall_ge_iff
  intro k
  rw [Int.toNat_le,Int.ceil_le,Int.cast_natCast,div_le_iff₀ hd',
    ← Nat.ceilDiv_eq_add_pred_div,ceilDiv_le_iff_le_mul (Nat.pos_of_ne_zero hd),
    Int.toNat_le]
  push_cast
  rw [mul_comm]
  norm_cast

@[simp] lemma eval_ceilRatioNat (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (ceilRatioNat a b).eval x=(Int.ceil ((a.eval x:ℚ)/(b.eval x:ℚ))).toNat := by
  simp only [ceilRatioNat,NatExpr.eval,eval_toNat,ceil_ratio_nat]

@[simp] lemma eval_floorRatio (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (floorRatio a b).eval x=Int.floor ((a.eval x:ℚ)/(b.eval x:ℚ)) := by
  simp only [floorRatio,eval_sub,eval_ofNat,NatExpr.eval,eval_toNat,eval_ceilRatioNat,
    eval_negation]
  by_cases hz : 0 ≤ a.eval x
  · have hc : Int.ceil (((-a.eval x:ℤ):ℚ)/(b.eval x:ℚ)) ≤ 0 := by
      rw [Int.ceil_le,Int.cast_zero]
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast neg_nonpos.mpr hz) (by positivity)
    rw [Int.toNat_of_nonpos hc,Int.natCast_zero,sub_zero]
    rw [Int.natCast_ediv,← Rat.floor_natCast_div_natCast]
    congr 2
    exact_mod_cast Int.toNat_of_nonneg hz
  · have hp : (a.eval x).toNat=0 := by omega
    rw [hp,Nat.zero_div,Int.natCast_zero,zero_sub]
    have hc : 0 ≤ Int.ceil (((-a.eval x:ℤ):ℚ)/(b.eval x:ℚ)) :=
      Int.ceil_nonneg (div_nonneg (by exact_mod_cast (show 0 ≤ -a.eval x by omega)) (by positivity))
    rw [Int.toNat_of_nonneg hc,Int.cast_neg,neg_div,Int.ceil_neg,neg_neg]

end IntExpr

namespace RatExpr
variable {v : Type*}
def ceilNat (a : RatExpr v) : NatExpr v := a.num.ceilRatioNat a.den
def floor (a : RatExpr v) : IntExpr v := a.num.floorRatio a.den
def ceil (a : RatExpr v) : IntExpr v := a.negation.floor.negation
@[simp] lemma eval_ceilNat (x : v → ℕ) (a : RatExpr v) :
    a.ceilNat.eval x=(Int.ceil (a.eval x)).toNat := by
  simp [ceilNat,eval]
@[simp] lemma eval_floor (x : v → ℕ) (a : RatExpr v) : a.floor.eval x=Int.floor (a.eval x) := by
  simp [floor,eval]
@[simp] lemma eval_ceil (x : v → ℕ) (a : RatExpr v) : a.ceil.eval x=Int.ceil (a.eval x) := by
  simp [ceil,Int.floor_neg]
end RatExpr
end ExactQuantumFactoring


end

end OAI
