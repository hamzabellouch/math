import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExpr

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open scoped ContDiff
variable {ι : Type*} [DecidableEq ι]

def logCurve (x : ι → ℝ) (i : ι) (t : ℝ) : ι → ℝ :=
  fun j => x j * Real.exp (if j = i then t else 0)

@[simp] theorem logCurve_zero (x : ι → ℝ) (i : ι) : logCurve x i 0 = x := by
  funext j
  simp [logCurve]

def logDerivative (x : ι → ℝ) (i : ι) : Expr ι → ℝ
  | .atom j => if j = i then x j else 0
  | .fixed _ => 0
  | .add a b => a.logDerivative x i + b.logDerivative x i
  | .sub a b => a.logDerivative x i - b.logDerivative x i
  | .mul a b => a.logDerivative x i * b.realEval x + a.realEval x * b.logDerivative x i
  | .divide a b => (a.logDerivative x i * b.realEval x - a.realEval x * b.logDerivative x i) /
      (b.realEval x) ^ 2

theorem hasDerivAt_logCurve (e : Expr ι) (x : ι → ℝ) (i : ι) (h : e.RealRegularAt x) :
    HasDerivAt (fun t => e.realEval (logCurve x i t)) (e.logDerivative x i) 0 := by
  induction e with
  | atom j =>
    by_cases hj : j = i
    · subst j
      simpa only [realEval, logDerivative, logCurve, ite_true, Real.exp_zero, mul_one] using
        (Real.hasDerivAt_exp 0).const_mul (x i)
    · simpa only [realEval, logDerivative, logCurve, ite_eq_right hj, Real.exp_zero, mul_one] using
        hasDerivAt_const (0 : ℝ) (x j)
  | fixed c => exact hasDerivAt_const _ _
  | add a b ia ib => simpa only [realEval, logDerivative] using (ia h.1).fun_add (ib h.2)
  | sub a b ia ib => simpa only [realEval, logDerivative] using (ia h.1).fun_sub (ib h.2)
  | mul a b ia ib =>
    simpa only [realEval, logDerivative, logCurve_zero] using (ia h.1).fun_mul (ib h.2)
  | divide a b ia ib =>
    simpa only [realEval, logDerivative, logCurve_zero] using
      (ia h.1).fun_div (ib h.2.1) (by simpa only [logCurve_zero] using h.2.2)

def logSlope (e : Expr ι) (x : ι → ℝ) (i : ι) : ℝ := e.logDerivative x i / e.realEval x

theorem logSlope_mul (a b : Expr ι) (x : ι → ℝ) (i : ι)
    (ha : a.realEval x ≠ 0) (hb : b.realEval x ≠ 0) :
    (Expr.mul a b).logSlope x i = a.logSlope x i + b.logSlope x i := by
  simp only [logSlope, logDerivative, realEval]
  field_simp

theorem logSlope_divide (a b : Expr ι) (x : ι → ℝ) (i : ι)
    (ha : a.realEval x ≠ 0) (hb : b.realEval x ≠ 0) :
    (Expr.divide a b).logSlope x i = a.logSlope x i - b.logSlope x i := by
  simp only [logSlope, logDerivative, realEval]
  field_simp

theorem logSlope_add (a b : Expr ι) (x : ι → ℝ) (i : ι)
    (ha : a.realEval x ≠ 0) (hb : b.realEval x ≠ 0)
    (he : (Expr.add a b).realEval x ≠ 0) :
    (Expr.add a b).logSlope x i =
      (a.realEval x / (Expr.add a b).realEval x) * a.logSlope x i +
      (b.realEval x / (Expr.add a b).realEval x) * b.logSlope x i := by
  simp only [logSlope, logDerivative, realEval] at he ⊢
  field_simp

theorem logSlope_sub (a b : Expr ι) (x : ι → ℝ) (i : ι)
    (ha : a.realEval x ≠ 0) (hb : b.realEval x ≠ 0)
    (he : (Expr.sub a b).realEval x ≠ 0) :
    (Expr.sub a b).logSlope x i =
      (a.realEval x / (Expr.sub a b).realEval x) * a.logSlope x i -
      (b.realEval x / (Expr.sub a b).realEval x) * b.logSlope x i := by
  simp only [logSlope, logDerivative, realEval] at he ⊢
  field_simp

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
