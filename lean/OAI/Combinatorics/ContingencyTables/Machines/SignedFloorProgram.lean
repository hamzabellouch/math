import OAI.Combinatorics.ContingencyTables.Machines.SignedPairProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps
import Mathlib.Data.Rat.Floor

namespace OAI

/-! # Binary floor of a signed rational

Two natural quotients and the comparison of their remainders compute
the exact floor. No loop depends on the numeric numerator or denominator.
-/

namespace ContingencyTables.SignedFloorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram

abbrev Input := Signed×ℕ

def numeratorQuotient (z : Input) : ℕ := z.1.1/z.2
def numeratorQuotientRealizer : Realizer numeratorQuotient :=
  composition (pair (composition first first) second) quotient
lemma polynomial_numeratorQuotient : PolynomialTime numeratorQuotientRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_quotient

def negativeQuotient (z : Input) : ℕ := z.1.2/z.2
def negativeQuotientRealizer : Realizer negativeQuotient :=
  composition (pair (composition first second) second) quotient
lemma polynomial_negativeQuotient : PolynomialTime negativeQuotientRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    polynomial_quotient

def carry (z : Input) : Bool := decide (z.1.1%z.2<z.1.2%z.2)
def carryRealizer : Realizer carry :=
  composition (pair
    (composition (pair (composition first first) second) remainder)
    (composition (pair (composition first second) second) remainder)) less
lemma polynomial_carry : PolynomialTime carryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_remainder)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_remainder)) polynomial_less

def carryValue (z : Input) : ℕ := if carry z then 1 else 0
def carryValueRealizer : Realizer carryValue :=
  choose carryRealizer (constant 1) (constant 0)
lemma polynomial_carryValue : PolynomialTime carryValueRealizer :=
  polynomial_choose polynomial_carry (polynomial_constant 1) (polynomial_constant 0)

def raw (z : Input) : Signed := (numeratorQuotient z,negativeQuotient z+carryValue z)
def rawRealizer : Realizer raw := pair numeratorQuotientRealizer
  (composition (pair negativeQuotientRealizer carryValueRealizer) add)
lemma polynomial_raw : PolynomialTime rawRealizer :=
  polynomial_pair polynomial_numeratorQuotient
    (polynomial_composition (polynomial_pair polynomial_negativeQuotient polynomial_carryValue)
      polynomial_add)

def floorCode (z : Input) : Signed := if z.2=0 then (0,0) else raw z
def floorCodeRealizer : Realizer floorCode :=
  (choose (composition (pair second (constant 0)) natEqual) (constant (0,0))
    rawRealizer).congr (fun z=>by simp only [floorCode,Function.comp_apply,decide_eq_true_eq])
theorem polynomial_floorCode : PolynomialTime floorCodeRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0))
      polynomial_natEqual) (polynomial_constant (0,0)) polynomial_raw)

lemma raw_value (p n d : ℕ) (hd : 0<d) :
    value (raw ((p,n),d))=⌊((p:ℚ)-n)/d⌋ := by
  have hdQ: (0:ℚ)<d:=by exact_mod_cast hd
  have hp: ((p%d:ℕ):ℚ)+(d:ℚ)*((p/d:ℕ):ℚ)=(p:ℚ):=by
    exact_mod_cast Nat.mod_add_div p d
  have hn: ((n%d:ℕ):ℚ)+(d:ℚ)*((n/d:ℕ):ℚ)=(n:ℚ):=by
    exact_mod_cast Nat.mod_add_div n d
  have hpr: ((p%d:ℕ):ℚ)<d:=by exact_mod_cast Nat.mod_lt p hd
  have hnr: ((n%d:ℕ):ℚ)<d:=by exact_mod_cast Nat.mod_lt n hd
  have hp0: (0:ℚ)≤((p%d:ℕ):ℚ):=Nat.cast_nonneg _
  have hn0: (0:ℚ)≤((n%d:ℕ):ℚ):=Nat.cast_nonneg _
  symm
  apply Int.floor_eq_iff.mpr
  by_cases h: p%d<n%d
  · have hr: ((p%d:ℕ):ℚ)<((n%d:ℕ):ℚ):=by exact_mod_cast h
    simp only [raw,numeratorQuotient,negativeQuotient,carryValue,carry,h,decide_true,
      ite_true,value,Nat.cast_add,Nat.cast_one,Int.cast_sub,
      Int.cast_add,Int.cast_one,Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hdQ]
      nlinarith
    · rw [div_lt_iff₀ hdQ]
      nlinarith
  · have hr: ((n%d:ℕ):ℚ)≤((p%d:ℕ):ℚ):=by exact_mod_cast (Nat.le_of_not_gt h)
    simp only [raw,numeratorQuotient,negativeQuotient,carryValue,carry,h,decide_false,
      Bool.false_eq_true,ite_false,Nat.add_zero,value,Int.cast_sub,Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hdQ]
      nlinarith
    · rw [div_lt_iff₀ hdQ]
      nlinarith

theorem floorCode_value (p n d : ℕ) :
    value (floorCode ((p,n),d))=⌊((p:ℚ)-n)/d⌋ := by
  by_cases hd: d=0
  · simp [floorCode,hd,value]
  · simp only [floorCode,hd,ite_false]
    exact raw_value p n d (Nat.pos_of_ne_zero hd)

abbrev ScaledInput := Input×List Bool

def scale (z : ScaledInput) : Input :=
  ((z.2.length*z.1.1.1,z.2.length*z.1.1.2),z.1.2)
def scaleRealizer : Realizer scale :=
  pair (pair
    (composition (pair (composition second listLength)
      (composition (composition first first) first)) multiply)
    (composition (pair (composition second listLength)
      (composition (composition first first) second)) multiply)) (composition first second)
lemma polynomial_scale : PolynomialTime scaleRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first)) polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second)) polynomial_multiply))
    (polynomial_composition polynomial_first polynomial_second)

def scaledFloor (z : ScaledInput) : Signed := floorCode (scale z)
def scaledFloorRealizer : Realizer scaledFloor := composition scaleRealizer floorCodeRealizer
theorem polynomial_scaledFloor : PolynomialTime scaledFloorRealizer :=
  polynomial_composition polynomial_scale polynomial_floorCode

theorem scaledFloor_value (p n d : ℕ) (xs : List Bool) :
    value (scaledFloor (((p,n),d),xs))=
      ⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋ := by
  rw [scaledFloor,scale,floorCode_value]
  congr 1
  push_cast
  ring

end ContingencyTables.SignedFloorProgram

end OAI
