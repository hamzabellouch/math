import Mathlib
import OAI.Computability.QuantumFactoring.FilterExpressionSyntax
import OAI.Computability.QuantumFactoring.ProgressionExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}
def pow (a : NatExpr v) : ℕ → NatExpr v
  | 0 => .const 1
  | n+1 => .mul (pow a n) a
@[simp] lemma eval_pow (x : v → ℕ) (a : NatExpr v) (n : ℕ) :
    (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => simp [pow,eval,ih,pow_succ]
end NatExpr

namespace RatExpr
variable {v : Type*}
def sumList {α : Type*} (f : α → RatExpr v) : List α → RatExpr v
  | [] => 0
  | a::as => f a+sumList f as
@[simp] lemma eval_sumList {α : Type*} (x : v → ℕ) (f : α → RatExpr v) (as : List α) :
    (sumList f as).eval x=(as.map (fun a => (f a).eval x)).sum := by
  induction as with
  | nil => simp [sumList]
  | cons a as ih => simp [sumList,ih]
end RatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def rampPoly (q a : ℤ) : PolyExpr v :=
  if a ≤ q then (.X-.const ((a:ℚ)/4))^2 else 0
def rampLin (q a : ℤ) : PolyExpr v :=
  if a ≤ q then .X-.const ((a:ℚ)/4) else 0
lemma rampPoly_correct (x : v → ℕ) (q a : ℤ) :
    (rampPoly q a).eval x=rampPiece q a := by
  by_cases h : a ≤ q <;> simp [rampPoly,rampPiece,h,PolyExpr.eval]
lemma rampLin_correct (x : v → ℕ) (q a : ℤ) :
    (rampLin q a).eval x=rampLinear q a := by
  by_cases h : a ≤ q <;> simp [rampLin,rampLinear,h,PolyExpr.eval]

def splineRePoly (q : ℤ) : PolyExpr v :=
  -(.X+.const (1/2))+2*(.X+.const (1/2))^2-4*rampPoly q 0+
    4*rampPoly q 2-4*rampPoly q 4
def splineImPoly (q : ℤ) : PolyExpr v :=
  2*(.X+.const (1/2))^2-4*rampPoly q (-1)+4*rampPoly q 1-
    4*rampPoly q 3+4*rampPoly q 5-.const (1/4)
def phaseRePoly (q : ℤ) : PolyExpr v :=
  -1+4*(.X+.const (1/2))-8*rampLin q 0+8*rampLin q 2-8*rampLin q 4
def phaseImPoly (q : ℤ) : PolyExpr v :=
  4*(.X+.const (1/2))-8*rampLin q (-1)+8*rampLin q 1-
    8*rampLin q 3+8*rampLin q 5
lemma splineRePoly_correct (x : v → ℕ) (q : ℤ) :
    (splineRePoly q).eval x=splineRePiece q := by
  simp [splineRePoly,splineRePiece,rampPoly_correct,PolyExpr.eval]
lemma splineImPoly_correct (x : v → ℕ) (q : ℤ) :
    (splineImPoly q).eval x=splineImPiece q := by
  simp [splineImPoly,splineImPiece,rampPoly_correct,PolyExpr.eval]
lemma phaseRePoly_correct (x : v → ℕ) (q : ℤ) :
    (phaseRePoly q).eval x=phaseRePiece q := by
  simp [phaseRePoly,phaseRePiece,rampLin_correct,PolyExpr.eval]
lemma phaseImPoly_correct (x : v → ℕ) (q : ℤ) :
    (phaseImPoly q).eval x=phaseImPiece q := by
  simp [phaseImPoly,phaseImPiece,rampLin_correct,PolyExpr.eval]

def linearPoly (d : NatExpr v) (η : RatExpr v) : PolyExpr v := .C ((ofNat d)⁻¹)*.X+.C η
lemma linearPoly_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) :
    (linearPoly d η).eval x=linearArg (d.eval x) (η.eval x) := by
  simp [linearPoly,linearArg,PolyExpr.eval]

def integralZero (d : NatExpr v) (A : PolyExpr v) : PolyExpr v :=
  .C ((ofNat d)⁻¹)*A.comp (linearPoly d 0)
def integralSlope (d : NatExpr v) (η : RatExpr v) (G₀ G₁ : PolyExpr v) : PolyExpr v :=
  .C ((ofNat d*η)⁻¹)*(G₁.comp (linearPoly d η)-G₀.comp (linearPoly d 0))
def massZero (d : NatExpr v) (q₀ : ℤ) : PolyExpr v :=
  integralZero d (phaseRePoly q₀)^2+integralZero d (phaseImPoly q₀)^2
def massSlope (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) : PolyExpr v :=
  integralSlope d η (splineRePoly q₀) (splineRePoly q₁)^2+
  integralSlope d η (splineImPoly q₀) (splineImPoly q₁)^2

def massCoeff (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) (k : ℕ) : RatExpr v :=
  ifEq η 0 ((massZero d q₀).coeff k) ((massSlope d η q₀ q₁).coeff k)
lemma massCoeff_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) (k : ℕ) :
    (massCoeff d η q₀ q₁ k).eval x=(massPiece (d.eval x) (η.eval x) q₀ q₁).coeff k := by
  by_cases h : η.eval x=0 <;>
    simp [massCoeff,RatExpr.eval_ifEq,PolyExpr.coeff_correct,h,massPiece,integralPiece,
      massZero,massSlope,integralZero,integralSlope,linearPoly_correct,
      phaseRePoly_correct,phaseImPoly_correct,splineRePoly_correct,splineImPoly_correct,
      PolyExpr.eval]

def rounded (D : NatExpr v) (a : RatExpr v) : RatExpr v :=
  ofInt (ofNat D*a).ceil/ofNat D
lemma rounded_correct (x : v → ℕ) (D : NatExpr v) (a : RatExpr v) :
    (rounded D a).eval x=roundCoeff (D.eval x) (a.eval x) := by
  simp [rounded,roundCoeff]

def roundingDen (Q B : NatExpr v) : NatExpr v := .mul Q (NatExpr.pow B 8)
lemma roundingDen_correct (x : v → ℕ) (Q B : NatExpr v) :
    (roundingDen Q B).eval x=Q.eval x*(B.eval x)^8 := by
  simp [roundingDen,NatExpr.eval]

def low (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) : NatExpr v :=
  NatExpr.max (ofNat d*const q.1/4).ceilNat (ofNat d*(const q.2/4-η)).ceilNat
def high (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) : NatExpr v :=
  NatExpr.min d (NatExpr.min (ofNat d*(const q.1+1)/4).ceilNat
    (ofNat d*((const q.2+1)/4-η)).ceilNat)
lemma low_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) :
    (low d η q).eval x=pieceLo (d.eval x) (η.eval x) q := by
  simp [low,pieceLo,intervalLo]
lemma high_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) :
    (high d η q).eval x=pieceHi (d.eval x) (η.eval x) q := by
  simp [high,pieceHi,intervalHi]

def pieceSum (Q B d j : NatExpr v) (q : ℤ×ℤ) : RatExpr v :=
  let η := error Q d j
  let lo := low d η q
  let hi := high d η q
  fiveTerm (fun k => rounded (roundingDen Q B) (massCoeff d η q.1 q.2 k)) lo hi+
    ofNat (.sub hi lo)*(64/ofNat Q)
lemma pieceSum_correct (x : v → ℕ) (Q B d j : NatExpr v) (q : ℤ×ℤ) :
    (pieceSum Q B d j q).eval x=packedPieceSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x) q := by
  simp [pieceSum,packedPieceSum,fiveTerm_correct,rounded_correct,roundingDen_correct,
    massCoeff_correct,error_correct,low_correct,high_correct,NatExpr.eval]

/-- Literal fixed 32-piece table; no noncomputable Finset enumeration is used
by the circuit generator. -/
def quarterList : List (ℤ×ℤ) :=
  ([0,1,2,3] : List ℤ).flatMap (fun q => ([-2,-1,0,1,2,3,4,5] : List ℤ).map (q,·))
lemma quarterList_nodup : quarterList.Nodup := by decide
lemma quarterList_finset : quarterList.toFinset=quarterPairs := by decide

def majorantSumE (Q B d j : NatExpr v) : RatExpr v :=
  sumList (pieceSum Q B d j) quarterList/2
lemma majorantSumE_correct (x : v → ℕ) (Q B d j : NatExpr v) :
    (majorantSumE Q B d j).eval x=packedMajorantSum (Q.eval x) (B.eval x) (d.eval x) (j.eval x) := by
  simp only [majorantSumE,RatExpr.eval_over,RatExpr.eval_num,RatExpr.eval_sumList,
    pieceSum_correct,packedMajorantSum]
  rw [← List.sum_toFinset _ quarterList_nodup,quarterList_finset]
  norm_num

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
