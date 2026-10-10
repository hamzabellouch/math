import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionSharing

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}

lemma pow_size (a : NatExpr v) (k : ℕ) : (a.pow k).size=k*(a.size+1)+1 := by
  induction k with
  | zero=>simp [pow,size]
  | succ k ih=>simp only [pow,size,ih]; ring
lemma pow_sharedCost (a : NatExpr v) (k : ℕ) :
    (a.pow k).sharedCost=k*(a.sharedCost+1)+1 := by
  induction k with
  | zero=>simp [pow,sharedCost]
  | succ k ih=>simp only [pow,sharedCost,ih]; ring
lemma pow_maxConst (a : NatExpr v) (k : ℕ) : (a.pow k).maxConst ≤ Nat.max a.maxConst 1 := by
  induction k with
  | zero=>exact le_max_right _ _
  | succ k ih=>exact max_le ih (le_max_left _ _)

end NatExpr
namespace IntExpr
variable {v : Type*}

/-- Power of a balanced signed integer without the exponentially expanding
positive/negative multiplication tree. The sign test is static in parity and
uses only absolute value and linear-length natural-power expressions. -/
def signedPower (a : IntExpr v) (k : ℕ) : IntExpr v :=
  let M:=ofNat (a.natAbs.pow k)
  if Even k then M else iteLe a.neg a.pos M M.negation

@[simp] lemma eval_signedPower (x : v→ℕ) (a : IntExpr v) (k : ℕ) :
    (signedPower a k).eval x=(a.eval x)^k := by
  have hm : (ofNat (a.natAbs.pow k)).eval x=|a.eval x|^k := by
    simp only [eval_ofNat,NatExpr.eval_pow,eval_natAbs,Nat.cast_pow,Int.natCast_natAbs]
  unfold signedPower
  split_ifs with hk
  · rw [hm]
    exact hk.pow_abs _
  · rw [eval_iteLe,eval_negation,hm]
    have ho : Odd k := Nat.not_even_iff_odd.mp hk
    by_cases hp : a.neg.eval x≤a.pos.eval x
    · rw [ite_eq_left hp,abs_of_nonneg]
      dsimp only [eval]
      omega
    · rw [ite_eq_right hp,abs_of_neg,ho.neg_pow,neg_neg]
      dsimp only [eval]
      omega

lemma signedPower_size (a : IntExpr v) (k : ℕ) :
    (a.signedPower k).pos.size ≤ 4*(k+1)*(a.pos.size+a.neg.size+2) ∧
    (a.signedPower k).neg.size ≤ 4*(k+1)*(a.pos.size+a.neg.size+2) := by
  unfold signedPower
  split_ifs <;>
    simp only [ofNat,iteLe,negation,natAbs,NatExpr.size,NatExpr.pow_size] <;>
    constructor <;> nlinarith

lemma signedPower_sharedCost (a : IntExpr v) (k : ℕ) :
    (a.signedPower k).pos.sharedCost ≤ 6*(k+1)*(a.pos.sharedCost+a.neg.sharedCost+2) ∧
    (a.signedPower k).neg.sharedCost ≤ 6*(k+1)*(a.pos.sharedCost+a.neg.sharedCost+2) := by
  unfold signedPower
  split_ifs <;>
    simp only [ofNat,iteLe,negation,natAbs,NatExpr.sharedCost,NatExpr.pow_sharedCost] <;>
    constructor <;> nlinarith

lemma signedPower_maxConst (a : IntExpr v) (k : ℕ) :
    (a.signedPower k).pos.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 ∧
    (a.signedPower k).neg.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 := by
  have hp := NatExpr.pow_maxConst a.natAbs k
  have he : a.natAbs.maxConst=max a.pos.maxConst a.neg.maxConst := by
    simp only [natAbs,NatExpr.maxConst]
    omega
  rw [he] at hp
  have h₁ : a.pos.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have h₂ : a.neg.maxConst ≤ max (max a.pos.maxConst a.neg.maxConst) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  unfold signedPower
  split_ifs <;> simp only [ofNat,iteLe,negation,NatExpr.maxConst]
  · exact ⟨hp,Nat.zero_le _⟩
  · simp only [max_le_iff]
    exact ⟨⟨⟨h₂,h₁⟩,hp,Nat.zero_le _⟩,⟨⟨h₂,h₁⟩,Nat.zero_le _,hp⟩⟩
end IntExpr
namespace RatExpr
variable {v : Type*}

/-- Exact rational power, with polynomial syntax in k, including zero
unreduced denominators. Existing `pow` and its semantics are not changed. -/
def signedPower (a : RatExpr v) (k : ℕ) : RatExpr v :=
  ⟨a.num.signedPower k,a.den.pow k⟩

@[simp] lemma eval_signedPower (x : v→ℕ) (a : RatExpr v) (k : ℕ) :
    (a.signedPower k).eval x=(a.eval x)^k := by
  simp only [signedPower,eval,IntExpr.eval_signedPower,NatExpr.eval_pow,
    Int.cast_pow,Nat.cast_pow,div_pow]

/-- The repeated-success expression used by both real transitions, without
an exponentially expanded balanced-integer numerator syntax. -/
def repeatedSuccess (a : RatExpr v) (K : ℕ) : RatExpr v :=
  (const 1).sub (((const 1).sub a).signedPower K)
lemma repeatedSuccess_value (x : v→ℕ) (a : RatExpr v) (K : ℕ) :
    (a.repeatedSuccess K).eval x=1-(1-a.eval x)^K := by
  simp only [repeatedSuccess,eval_sub,eval_const,eval_signedPower]

end RatExpr
end ExactQuantumFactoring


end

end OAI
