import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprBound

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Characters.RationalHistory
open scoped ContDiff

theorem deriv_eq_zero_of_nonneg_of_eq_zero (f : ℝ → ℝ) (x : ℝ)
    (hn : ∀ t, 0 ≤ f t) (hx : f x = 0) : deriv f x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun t => by rw [hx]; exact hn t)

theorem giantCell_deriv_zero_of_eq_zero (G p : ℝ) (h : giantCell G p = 0) :
    deriv (giantCell G) p = 0 :=
  deriv_eq_zero_of_nonneg_of_eq_zero _ p (fun q => (giantCell_bounds G q).1) h

theorem giantCell_logCurve_deriv_bound : ∃ D : ℝ, 0 < D ∧
    ∀ {ι : Type} [DecidableEq ι] (e : Expr ι) (x : ι → ℝ) (i : ι) (G K : ℝ),
      1 ≤ K → e.RelativeControl x K →
      |deriv (fun t => giantCell G (e.realEval (Expr.logCurve x i t))) 0| ≤ D * e.logBudget K := by
  obtain ⟨D,hD,hDb⟩ := giantCell_log_deriv_bound
  refine ⟨D,hD,?_⟩
  intro ι _ e x i G K hK he
  have hc := e.hasDerivAt_logCurve x i (Expr.RelativeControl.regular e x K he)
  have hg := (((giantCell_contDiff G).differentiable (by simp)) (e.realEval x)).hasDerivAt
  have hcomp := hg.comp_of_eq 0 hc (by rw [Expr.logCurve_zero])
  simp only [Function.comp_def] at hcomp
  rw [hcomp.deriv]
  have hp := Expr.RelativeControl.value_ne_zero e x K he
  have hid : e.logDerivative x i = e.realEval x * e.logSlope x i := by
    unfold Expr.logSlope
    field_simp
  rw [hid,← mul_assoc,abs_mul,mul_comm (deriv (giantCell G) (e.realEval x))]
  exact mul_le_mul (hDb G (e.realEval x)) (Expr.logSlope_bound e x i hK he)
    (abs_nonneg _) hD.le

end Ostmann.Arithmetic

end

end OAI
