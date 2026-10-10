import Mathlib
import OAI.Computability.QuantumFactoring.RationalConditionals
import OAI.Computability.QuantumFactoring.RationalRounding
import OAI.Computability.QuantumFactoring.PolynomialExpressions
import OAI.Computability.QuantumFactoring.FilterExpressionSyntax
import OAI.Computability.QuantumFactoring.ProgressionEvaluation

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}
def min (a b : NatExpr v) : NatExpr v := .iteLe a b a b
def max (a b : NatExpr v) : NatExpr v := .iteLe a b b a
@[simp] lemma eval_min (x : v → ℕ) (a b : NatExpr v) : (min a b).eval x=Min.min (a.eval x) (b.eval x) := by
  simp [min,eval,min_def]
@[simp] lemma eval_max (x : v → ℕ) (a b : NatExpr v) : (max a b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp [max,eval,max_def]
end NatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def powerSum (q : ℕ) (M : RatExpr v) : RatExpr v := match q with
  | 0 => M
  | 1 => M*(M-1)/2
  | 2 => M*(M-1)*(2*M-1)/6
  | 3 => (M*(M-1)/2)^2
  | 4 => M*(M-1)*(2*M-1)*(3*M^2-3*M-1)/30
  | _ => 0
lemma powerSum_correct (x : v → ℕ) (q : ℕ) (M : RatExpr v) :
    (powerSum q M).eval x=powerSumValue q (M.eval x) := by
  rcases q with _|_|_|_|_|q <;> simp [powerSum,powerSumValue]

def fiveTerm (a : ℕ → RatExpr v) (lo hi : NatExpr v) : RatExpr v :=
  ifNatLe lo hi (RatExpr.sum (fun q => a q*(powerSum q (ofNat hi)-powerSum q (ofNat lo))) 5) 0
lemma fiveTerm_correct (x : v → ℕ) (a : ℕ → RatExpr v) (lo hi : NatExpr v) :
    (fiveTerm a lo hi).eval x=fiveTermSum (fun q => (a q).eval x) (lo.eval x) (hi.eval x) := by
  simp [fiveTerm,fiveTermSum,powerSum_correct]

def linear (a b : RatExpr v) (lo hi : NatExpr v) : RatExpr v :=
  fiveTerm (fun q => if q=0 then a else if q=1 then b else 0) lo hi
lemma linear_correct (x : v → ℕ) (a b : RatExpr v) (lo hi : NatExpr v) :
    (linear a b lo hi).eval x=linearSum (a.eval x) (b.eval x) (lo.eval x) (hi.eval x) := by
  rw [linear,fiveTerm_correct,linearSum]
  congr 1
  funext q
  split_ifs <;> simp

def ramp (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  ifLt 0 b (linear a b ((-a/b).ceilNat) M)
    (ifLt b 0 (linear a b (.const 0) (NatExpr.min M (-a/b).ceilNat))
      (ofNat M*RatExpr.max 0 a))
lemma ramp_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (ramp a b M).eval x=rampSum (a.eval x) (b.eval x) (M.eval x) := by
  simp [ramp,rampSum,linear_correct,NatExpr.eval]

def phaseRe (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  -ofNat M+4*linear (a+1/2) b (.const 0) M-8*ramp a b M+
    8*ramp (a-1/2) b M-8*ramp (a-1) b M
lemma phaseRe_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (phaseRe a b M).eval x=phaseSumRe (a.eval x) (b.eval x) (M.eval x) := by
  simp [phaseRe,phaseSumRe,linear_correct,ramp_correct,NatExpr.eval]

def phaseIm (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  4*linear (a+1/2) b (.const 0) M-8*ramp (a+1/4) b M+
    8*ramp (a-1/4) b M-8*ramp (a-3/4) b M+8*ramp (a-5/4) b M
lemma phaseIm_correct (x : v → ℕ) (a b : RatExpr v) (M : NatExpr v) :
    (phaseIm a b M).eval x=phaseSumIm (a.eval x) (b.eval x) (M.eval x) := by
  simp [phaseIm,phaseSumIm,linear_correct,ramp_correct,NatExpr.eval]

def binE (Q d j : NatExpr v) : NatExpr v :=
  .div (.add (.mul (.mul (.const 2) j) Q) d) (.mul (.const 2) d)
lemma binE_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (binE Q d j).eval x=bin (Q.eval x) (d.eval x) (j.eval x) := rfl

def error (Q d j : NatExpr v) : RatExpr v := ofNat (binE Q d j)-ofNat j*ofNat Q/ofNat d
lemma error_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (error Q d j).eval x=binErrorRat (Q.eval x) (d.eval x) (j.eval x) := by
  simp [error,binErrorRat,binE_correct]

def offset (Q d j t : NatExpr v) : RatExpr v :=
  ofNat (.mod (.mul j t) d)/ofNat d+error Q d j*ofNat t/ofNat Q
lemma offset_correct (x : v → ℕ) (Q d j t : NatExpr v) :
    (offset Q d j t).eval x=sampleOffset (Q.eval x) (d.eval x) (j.eval x) (t.eval x) := by
  simp [offset,sampleOffset,error_correct,NatExpr.eval]

def slope (Q d j : NatExpr v) : RatExpr v := error Q d j*ofNat d/ofNat Q
lemma slope_correct (x : v → ℕ) (Q d j : NatExpr v) :
    (slope Q d j).eval x=sampleSlope (Q.eval x) (d.eval x) (j.eval x) := by
  simp [slope,sampleSlope,error_correct]

def count (Q d t : NatExpr v) : NatExpr v := .add (.div (.sub (.sub Q (.const 1)) t) d) (.const 1)
lemma count_correct (x : v → ℕ) (Q d t : NatExpr v) :
    (count Q d t).eval x=sampleCount (Q.eval x) (d.eval x) (t.eval x) := rfl

/-- A literal finite arithmetic template for P. Its size is independent of Q,
B,d,j,t; there is no enumeration of the phase-register range. -/
def probability (Q d j t : NatExpr v) : RatExpr v :=
  (phaseRe (offset Q d j t) (slope Q d j) (count Q d t)^2+
   phaseIm (offset Q d j t) (slope Q d j) (count Q d t)^2)/(ofNat Q)^2
lemma probability_correct (x : v → ℕ) (Q d j t : NatExpr v) :
    (probability Q d j t).eval x=fastResidueProbability (Q.eval x) (d.eval x) (j.eval x) (t.eval x) := by
  simp [probability,fastResidueProbability,phaseRe_correct,phaseIm_correct,
    offset_correct,slope_correct,count_correct]
end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
