import OAI.NumberTheory.Ostmann.Characters.RationalHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
open scoped ContDiff
variable {ι : Type*}

def realEval (x : ι → ℝ) : Expr ι → ℝ
  | .atom i => x i
  | .fixed c => c
  | .add a b => a.realEval x + b.realEval x
  | .sub a b => a.realEval x - b.realEval x
  | .mul a b => a.realEval x * b.realEval x
  | .divide a b => a.realEval x / b.realEval x

def RealRegularAt (x : ι → ℝ) : Expr ι → Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.RealRegularAt x ∧ b.RealRegularAt x
  | .sub a b => a.RealRegularAt x ∧ b.RealRegularAt x
  | .mul a b => a.RealRegularAt x ∧ b.RealRegularAt x
  | .divide a b => a.RealRegularAt x ∧ b.RealRegularAt x ∧ b.realEval x ≠ 0

theorem realEval_cast_rational (e : Expr ι) (x : ι → ℚ) :
    e.realEval (fun i => (x i : ℝ)) = (e.rationalEval x : ℝ) := by
  induction e with
  | atom i => rfl
  | fixed c => simp only [realEval, rationalEval, Rat.cast_intCast]
  | add a b ia ib => simp only [realEval, rationalEval, ia, ib, Rat.cast_add]
  | sub a b ia ib => simp only [realEval, rationalEval, ia, ib, Rat.cast_sub]
  | mul a b ia ib => simp only [realEval, rationalEval, ia, ib, Rat.cast_mul]
  | divide a b ia ib => simp only [realEval, rationalEval, ia, ib, Rat.cast_div]

theorem realRegularAt_cast_rational_iff (e : Expr ι) (x : ι → ℚ) :
    e.RealRegularAt (fun i => (x i : ℝ)) ↔ e.RegularAt x := by
  induction e with
  | atom i => rfl
  | fixed c => rfl
  | add a b ia ib => simp only [RealRegularAt, RegularAt, ia, ib]
  | sub a b ia ib => simp only [RealRegularAt, RegularAt, ia, ib]
  | mul a b ia ib => simp only [RealRegularAt, RegularAt, ia, ib]
  | divide a b ia ib =>
    simp only [RealRegularAt, RegularAt, ia, ib, realEval_cast_rational, ne_eq, Rat.cast_eq_zero]

theorem contDiffAt_realEval [Fintype ι] (e : Expr ι) (x : ι → ℝ) (h : e.RealRegularAt x) :
    ContDiffAt ℝ ∞ (fun y : ι → ℝ => e.realEval y) x := by
  induction e with
  | atom i => simpa only [realEval] using (show ContDiffAt ℝ ∞ (fun y : ι → ℝ => y i) x by fun_prop)
  | fixed c => exact contDiffAt_const
  | add a b ia ib => exact (ia h.1).add (ib h.2)
  | sub a b ia ib => exact (ia h.1).sub (ib h.2)
  | mul a b ia ib => exact (ia h.1).mul (ib h.2)
  | divide a b ia ib => exact (ia h.1).div (ib h.2.1) h.2.2

def logEval (e : Expr ι) (y : ι → ℝ) : ℝ := e.realEval (fun i => Real.exp (y i))

theorem contDiffAt_logEval [Fintype ι] (e : Expr ι) (x : ι → ℝ)
    (h : e.RealRegularAt (fun i => Real.exp (x i))) :
    ContDiffAt ℝ ∞ (e.logEval) x := by
  exact (e.contDiffAt_realEval _ h).comp x
    (show ContDiffAt ℝ ∞ (fun y : ι → ℝ => fun i => Real.exp (y i)) x by fun_prop)

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
