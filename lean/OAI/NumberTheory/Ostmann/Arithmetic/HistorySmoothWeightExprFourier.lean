import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightFourier

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Characters.RationalHistory Filter
open scoped SchwartzMap Topology
variable {ι : Type*} [DecidableEq ι]

def exprLeafScalar (ρ : 𝓢(ℝ, ℂ)) (v X : ℝ) (e : Expr ι) (x : ι → ℝ) : ℂ :=
  (Real.sqrt (X / e.realEval x):ℂ) * ρ (-v * X / e.realEval x)

theorem exprLeafScalar_logCurve_deriv_bound (ρ : 𝓢(ℝ, ℂ)) (v X : ℝ) (e : Expr ι)
    (x : ι → ℝ) (i : ι) (K : ℝ) (hX : 0 < X) (hepos : 0 < e.realEval x)
    (hK : 1 ≤ K) (he : e.RelativeControl x K) :
    ‖deriv (fun t => exprLeafScalar ρ v X e (Expr.logCurve x i t)) 0‖ ≤
      Real.sqrt (X / e.realEval x) * leafProfileBound ρ * e.logBudget K := by
  have hc := e.hasDerivAt_logCurve x i (Expr.RelativeControl.regular e x K he)
  have hlog : HasDerivAt (fun t => Real.log (e.realEval (Expr.logCurve x i t))) (e.logSlope x i) 0 := by
    simpa only [Expr.logCurve_zero,Expr.logSlope] using
      hc.log (by simpa only [Expr.logCurve_zero] using hepos.ne')
  have harg := hlog.const_sub (Real.log X)
  let z := Real.log X - Real.log (e.realEval x)
  have hp := (leafLogProfile_hasDerivAt ρ v z).differentiableAt.hasDerivAt
  have hcomp := hp.scomp_of_eq 0 harg (by simp only [z,Expr.logCurve_zero])
  have heq : (fun t => exprLeafScalar ρ v X e (Expr.logCurve x i t)) =ᶠ[𝓝 0]
      (fun t => leafLogProfile ρ v (Real.log X - Real.log (e.realEval (Expr.logCurve x i t)))) := by
    have hcpos : ∀ᶠ t in 𝓝 0, 0 < e.realEval (Expr.logCurve x i t) :=
      hc.continuousAt.eventually (eventually_gt_nhds (by simpa only [Expr.logCurve_zero] using hepos))
    filter_upwards [hcpos] with t ht
    rw [← Real.log_div hX.ne' ht.ne',leafLogProfile_eq_scalar ρ v X _ hX ht]
    rfl
  have hder : HasDerivAt (fun t => exprLeafScalar ρ v X e (Expr.logCurve x i t))
      ((-e.logSlope x i) • deriv (leafLogProfile ρ v) z) 0 := by
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    simpa only [Function.comp_def] using hcomp
  rw [hder.deriv,norm_smul,Real.norm_eq_abs,abs_neg]
  have hz : Real.exp (z/2) = Real.sqrt (X / e.realEval x) := by
    rw [show z = Real.log (X / e.realEval x) by exact (Real.log_div hX.ne' hepos.ne').symm]
    exact exp_half_log_eq_sqrt (div_pos hX hepos)
  have hρ := leafLogProfile_deriv_bound ρ v z
  rw [hz] at hρ
  calc
    _ ≤ e.logBudget K * (Real.sqrt (X / e.realEval x) * leafProfileBound ρ) :=
      mul_le_mul (Expr.logSlope_bound e x i hK he) hρ (norm_nonneg _)
        (Expr.logBudget_nonneg e (zero_le_one.trans hK))
    _ = _ := by ring

end Ostmann.Arithmetic

end

end OAI
