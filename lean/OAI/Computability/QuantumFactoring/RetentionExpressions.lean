import Mathlib
import OAI.Computability.QuantumFactoring.DynamicMajorantExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
open RatExpr
variable {v : Type*}

/-- Bounded priority search for the least covering power of two.  The bounds
are compile-time constants, not exponentiation gates with variable exponents. -/
def coveringPow (d : NatExpr v) : ℕ → NatExpr v
  | 0 => .const 1
  | k+1 => .iteLe d (.const (2^k)) (coveringPow d k) (.const (2^(k+1)))
lemma coveringPow_correct (x : v → ℕ) (d : NatExpr v) (n : ℕ)
    (hd : d.eval x≤2^n) : (coveringPow d n).eval x=2^(Nat.clog 2 (d.eval x)) := by
  induction n with
  | zero =>
    have hc : Nat.clog 2 (d.eval x)=0 := Nat.eq_zero_of_le_zero (Nat.clog_le_of_le_pow hd)
    simp [coveringPow,NatExpr.eval,hc]
  | succ n ih =>
    change (if d.eval x≤2^n then (coveringPow d n).eval x else 2^(n+1))=_
    by_cases h : d.eval x≤2^n
    · rw [ite_eq_left h]; exact ih h
    · have hc : Nat.clog 2 (d.eval x)=n+1 := by
        have h₁ := Nat.clog_le_of_le_pow hd
        have h₂ := (Nat.lt_clog_iff_pow_lt (by omega : 1<2)).mpr (Nat.lt_of_not_ge h)
        omega
      rw [ite_eq_right h,hc]

def lambdaE (n : ℕ) (d : NatExpr v) : RatExpr v :=
  1/ofNat (.mul (.const 1024) (coveringPow d n))
lemma lambdaE_correct (x : v → ℕ) (n : ℕ) (d : NatExpr v) (hd : d.eval x≤2^n) :
    (lambdaE n d).eval x=prescribedMass (d.eval x) := by
  simp [lambdaE,coveringPow_correct x d n hd,prescribedMass,NatExpr.eval,pow_add]
  ring

def coefficientE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  ofInt ((ofNat (.const (2^(10*n))) * lambdaE n d / majorantSumE Q B d j).floor) /
    ofNat (.const (2^(10*n)))
lemma coefficientE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (coefficientE n Q B d j).eval x=
      modeCoeff n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [coefficientE,lambdaE_correct x n d hd,majorantSumE_correct,packedMajorantSum_correct hpos,modeCoeff,NatExpr.eval,mul_div_assoc]

def remainderE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  lambdaE n d - coefficientE n Q B d j * majorantSumE Q B d j
lemma remainderE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (remainderE n Q B d j).eval x=
      modeRemainder n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [remainderE,lambdaE_correct x n d hd,coefficientE_correct x n Q B d j hd hpos,
    majorantSumE_correct,packedMajorantSum_correct hpos,modeRemainder]

def discrepancyE (n : ℕ) (Q B d j t : NatExpr v) : RatExpr v :=
  2*(ofNat B)^3*(majorantE Q B d j (.mod (.mul j t) d)-probability Q d j t)*coefficientE n Q B d j
lemma discrepancyE_correct (x : v → ℕ) (n : ℕ) (Q B d j t : NatExpr v) (hd : d.eval x≤2^n)
    (hdt : 0<d.eval x) (ht : t.eval x<d.eval x) (hdQ : d.eval x≤Q.eval x) :
    (discrepancyE n Q B d j t).eval x =
      2*(B.eval x:ℚ)^3*(majorant (Q.eval x) (B.eval x) (d.eval x) (j.eval x)
        ((j.eval x*t.eval x)%d.eval x)-residueProbabilityRat (Q.eval x) (d.eval x) (j.eval x) (t.eval x))*
        modeCoeff n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [discrepancyE,majorantE_correct,coefficientE_correct x n Q B d j hd hdt,NatExpr.eval,
    probability_correct,fastResidueProbability_eq hdt hdQ ht]

def thirdRetentionE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  4*(ofNat B)^2*remainderE n Q B d j
lemma thirdRetentionE_correct (x : v → ℕ) (n : ℕ) (Q B d j : NatExpr v) (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (thirdRetentionE n Q B d j).eval x=4*(B.eval x:ℚ)^2*
      modeRemainder n (prescribedMass (d.eval x)) (majorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x)) := by
  simp [thirdRetentionE,remainderE_correct x n Q B d j hd hpos]

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI
