import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprControl

namespace OAI

noncomputable section
namespace Ostmann.Characters.RationalHistory.Expr
variable {ι : Type*} [DecidableEq ι]

theorem abs_sub_le_abs_sum (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

omit [DecidableEq ι] in
theorem logBudget_cancel_le (a b : Expr ι) {K : ℝ} (hK : 1 ≤ K) :
    K * a.logBudget K + K * b.logBudget K ≤
      ((a.logSize + b.logSize : ℕ) : ℝ) * K ^ (max a.cancellationDepth b.cancellationDepth + 1) := by
  have h := mul_le_mul_of_nonneg_left (logBudget_add_le_max a b hK) (zero_le_one.trans hK)
  simpa only [pow_succ, mul_add, mul_assoc, mul_left_comm, mul_comm] using h

theorem logSlope_bound (e : Expr ι) (x : ι → ℝ) (i : ι) {K : ℝ}
    (hK : 1 ≤ K) (h : e.RelativeControl x K) : |e.logSlope x i| ≤ e.logBudget K := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  induction e with
  | atom j =>
    by_cases hj : j = i
    · subst j
      simp only [logSlope, logDerivative, realEval, ite_true, div_self (show x i ≠ 0 from h),
        abs_one, logBudget, logSize, cancellationDepth, Nat.cast_one, pow_zero, mul_one, le_refl]
    · simp only [logSlope, logDerivative, realEval, hj, ite_false, zero_div, abs_zero,
        logBudget, logSize, cancellationDepth, Nat.cast_one, pow_zero, mul_one, zero_le_one]
  | fixed c => simp [logSlope, logDerivative, realEval, logBudget, logSize, cancellationDepth]
  | add a b ia ib =>
    rw [logSlope_add a b x i (RelativeControl.value_ne_zero a x K h.1)
      (RelativeControl.value_ne_zero b x K h.2.1) h.2.2.1]
    calc
      _ ≤ |a.realEval x / (Expr.add a b).realEval x| * |a.logSlope x i| +
          |b.realEval x / (Expr.add a b).realEval x| * |b.logSlope x i| := by
        simpa only [abs_mul] using abs_add_le
          ((a.realEval x / (Expr.add a b).realEval x) * a.logSlope x i)
          ((b.realEval x / (Expr.add a b).realEval x) * b.logSlope x i)
      _ ≤ K * a.logBudget K + K * b.logBudget K := add_le_add
        (mul_le_mul h.2.2.2.1 (ia h.1) (abs_nonneg _) hK0)
        (mul_le_mul h.2.2.2.2 (ib h.2.1) (abs_nonneg _) hK0)
      _ ≤ _ := logBudget_cancel_le a b hK
  | sub a b ia ib =>
    rw [logSlope_sub a b x i (RelativeControl.value_ne_zero a x K h.1)
      (RelativeControl.value_ne_zero b x K h.2.1) h.2.2.1]
    calc
      _ ≤ |a.realEval x / (Expr.sub a b).realEval x| * |a.logSlope x i| +
          |b.realEval x / (Expr.sub a b).realEval x| * |b.logSlope x i| := by
        simpa only [abs_mul] using abs_sub_le_abs_sum
          ((a.realEval x / (Expr.sub a b).realEval x) * a.logSlope x i)
          ((b.realEval x / (Expr.sub a b).realEval x) * b.logSlope x i)
      _ ≤ K * a.logBudget K + K * b.logBudget K := add_le_add
        (mul_le_mul h.2.2.2.1 (ia h.1) (abs_nonneg _) hK0)
        (mul_le_mul h.2.2.2.2 (ib h.2.1) (abs_nonneg _) hK0)
      _ ≤ _ := logBudget_cancel_le a b hK
  | mul a b ia ib =>
    rw [logSlope_mul a b x i (RelativeControl.value_ne_zero a x K h.1)
      (RelativeControl.value_ne_zero b x K h.2)]
    exact (abs_add_le _ _).trans ((add_le_add (ia h.1) (ib h.2)).trans
      (logBudget_add_le_max a b hK))
  | divide a b ia ib =>
    rw [logSlope_divide a b x i (RelativeControl.value_ne_zero a x K h.1)
      (RelativeControl.value_ne_zero b x K h.2)]
    exact (abs_sub_le_abs_sum _ _).trans ((add_le_add (ia h.1) (ib h.2)).trans
      (logBudget_add_le_max a b hK))

theorem deriv_logCurve_bound (e : Expr ι) (x : ι → ℝ) (i : ι) {K : ℝ}
    (hK : 1 ≤ K) (h : e.RelativeControl x K) :
    |deriv (fun t => e.realEval (logCurve x i t)) 0| ≤ |e.realEval x| * e.logBudget K := by
  rw [(e.hasDerivAt_logCurve x i (RelativeControl.regular e x K h)).deriv]
  have he := RelativeControl.value_ne_zero e x K h
  have heq : e.logDerivative x i = e.realEval x * e.logSlope x i := by
    dsimp [logSlope]
    field_simp
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_left (logSlope_bound e x i hK h) (abs_nonneg _)

end Ostmann.Characters.RationalHistory.Expr

end

end OAI
