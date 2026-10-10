import Mathlib
import OAI.Computability.QuantumFactoring.PolynomialFilterExpressions

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def dynamicRamp (q : IntExpr v) (a : ℤ) : PolyExpr v :=
  .C (ifIntLe (.ofInt a) q 1 0)*(.X-.const ((a:ℚ)/4))^2
def dynamicRampLin (q : IntExpr v) (a : ℤ) : PolyExpr v :=
  .C (ifIntLe (.ofInt a) q 1 0)*(.X-.const ((a:ℚ)/4))
lemma dynamicRamp_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRamp q a).eval x=rampPiece (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRamp,rampPiece,h,PolyExpr.eval]
lemma dynamicRampLin_correct (x : v → ℕ) (q : IntExpr v) (a : ℤ) :
    (dynamicRampLin q a).eval x=rampLinear (q.eval x) a := by
  by_cases h : a ≤ q.eval x <;> simp [dynamicRampLin,rampLinear,h,PolyExpr.eval]

def dynamicSplineRe (q : IntExpr v) : PolyExpr v :=
  -(.X+.const (1/2))+2*(.X+.const (1/2))^2-4*dynamicRamp q 0+
    4*dynamicRamp q 2-4*dynamicRamp q 4
def dynamicSplineIm (q : IntExpr v) : PolyExpr v :=
  2*(.X+.const (1/2))^2-4*dynamicRamp q (-1)+4*dynamicRamp q 1-
    4*dynamicRamp q 3+4*dynamicRamp q 5-.const (1/4)
def dynamicPhaseRe (q : IntExpr v) : PolyExpr v :=
  -1+4*(.X+.const (1/2))-8*dynamicRampLin q 0+8*dynamicRampLin q 2-8*dynamicRampLin q 4
def dynamicPhaseIm (q : IntExpr v) : PolyExpr v :=
  4*(.X+.const (1/2))-8*dynamicRampLin q (-1)+8*dynamicRampLin q 1-
    8*dynamicRampLin q 3+8*dynamicRampLin q 5
lemma dynamicSplineRe_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicSplineRe q).eval x=splineRePiece (q.eval x) := by
  simp [dynamicSplineRe,splineRePiece,dynamicRamp_correct,PolyExpr.eval]
lemma dynamicSplineIm_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicSplineIm q).eval x=splineImPiece (q.eval x) := by
  simp [dynamicSplineIm,splineImPiece,dynamicRamp_correct,PolyExpr.eval]
lemma dynamicPhaseRe_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicPhaseRe q).eval x=phaseRePiece (q.eval x) := by
  simp [dynamicPhaseRe,phaseRePiece,dynamicRampLin_correct,PolyExpr.eval]
lemma dynamicPhaseIm_correct (x : v → ℕ) (q : IntExpr v) :
    (dynamicPhaseIm q).eval x=phaseImPiece (q.eval x) := by
  simp [dynamicPhaseIm,phaseImPiece,dynamicRampLin_correct,PolyExpr.eval]


def dynamicMassZero (d : NatExpr v) (q₀ : IntExpr v) : PolyExpr v :=
  integralZero d (dynamicPhaseRe q₀)^2+integralZero d (dynamicPhaseIm q₀)^2
def dynamicMassSlope (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : IntExpr v) : PolyExpr v :=
  integralSlope d η (dynamicSplineRe q₀) (dynamicSplineRe q₁)^2+
    integralSlope d η (dynamicSplineIm q₀) (dynamicSplineIm q₁)^2

def dynamicMassCoeff (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : IntExpr v) (k : ℕ) : RatExpr v :=
  ifEq η 0 ((dynamicMassZero d q₀).coeff k) ((dynamicMassSlope d η q₀ q₁).coeff k)
lemma dynamicMassCoeff_correct (x : v → ℕ) (d : NatExpr v) (η : RatExpr v)
    (q₀ q₁ : IntExpr v) (k : ℕ) :
    (dynamicMassCoeff d η q₀ q₁ k).eval x=
      (massPiece (d.eval x) (η.eval x) (q₀.eval x) (q₁.eval x)).coeff k := by
  by_cases h : η.eval x=0 <;>
    simp [dynamicMassCoeff,RatExpr.eval_ifEq,PolyExpr.coeff_correct,h,massPiece,integralPiece,
      dynamicMassZero,dynamicMassSlope,integralZero,integralSlope,linearPoly_correct,
      dynamicPhaseRe_correct,dynamicPhaseIm_correct,dynamicSplineRe_correct,dynamicSplineIm_correct,
      PolyExpr.eval]

def quarter (a : RatExpr v) : IntExpr v := (4*a).floor
lemma quarter_correct (x : v → ℕ) (a : RatExpr v) :
    (quarter a).eval x=quarterIndex (a.eval x) := by simp [quarter,quarterIndex]

/-- Actual constant-depth arithmetic for U, including dynamic quarter selection.
No residue loop and no polynomial-valued oracle occurs in this expression. -/
def majorantE (Q B d j u : NatExpr v) : RatExpr v :=
  let η := error Q d j
  let q₀ := quarter (ofNat u/ofNat d)
  let q₁ := quarter (ofNat u/ofNat d+η)
  RatExpr.sum (fun k => rounded (roundingDen Q B) (dynamicMassCoeff d η q₀ q₁ k)*(ofNat u)^k) 5+
    64/ofNat Q
lemma majorantE_correct (x : v → ℕ) (Q B d j u : NatExpr v) :
    (majorantE Q B d j u).eval x=
      majorant (Q.eval x) (B.eval x) (d.eval x) (j.eval x) (u.eval x) := by
  simp [majorantE,majorant,roundedValue,selectedMass,rounded_correct,roundingDen_correct,
    dynamicMassCoeff_correct,error_correct,quarter_correct]

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI
