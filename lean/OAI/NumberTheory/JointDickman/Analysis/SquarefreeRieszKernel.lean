import OAI.NumberTheory.JointDickman.Analysis.SquarefreeContourSeries
import OAI.NumberTheory.JointDickman.Analysis.FractionalContourShift

namespace OAI

/-! # The analytic factor of the Riesz--Perron contour integrand -/
namespace JointDickman
open Complex Filter
open scoped Topology

noncomputable def squarefreeRieszKernel (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  squarefreeAnalyticFactor z (1+w) * exp ((z:ℂ)*f (1+w)) * exp ((L:ℂ)*w) /
    ((1+w)*(2+w))

theorem squarefreeRieszKernel_factorization (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) :
    fractionalContourIntegrand z (squarefreeRieszKernel z L f) w =
      squarefreeContourSeries z f (1+w) * exp ((L:ℂ)*w) / ((1+w)*(2+w)) := by
  simp only [fractionalContourIntegrand,squarefreeRieszKernel,fractionalPowerKernel,
    squarefreeContourSeries,add_sub_cancel_left,mul_sub,Complex.exp_sub,Complex.exp_neg,neg_mul]
  ring

theorem squarefreeRieszKernel_analyticAt {z L : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f (1+w)) (hw : 1/2 < (1+w).re) :
    AnalyticAt ℂ (squarefreeRieszKernel z L f) w := by
  have hw1 : (1+w) ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hw2 : (2+w) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
    simp only [add_re,one_re] at hw
    linarith
  have ha : AnalyticAt ℂ (fun w : ℂ => 1+w) w := analyticAt_const.add analyticAt_id
  have hb : AnalyticAt ℂ (fun w : ℂ => 2+w) w := analyticAt_const.add analyticAt_id
  have hG := (squarefreeAnalyticFactor_analyticOnNhd hz hz1 (1+w) hw).comp ha
  have hlog := hf.comp ha
  exact (((hG.mul (analyticAt_const.mul hlog).cexp').mul
    (analyticAt_const.mul analyticAt_id).cexp').div (ha.mul hb) (mul_ne_zero hw1 hw2))

theorem squarefreeRieszKernel_norm {z L : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hw : w ≠ 0) (hf : exp (f (1+w)) = zetaPoleFactor (1+w)) :
    ‖fractionalContourIntegrand z (squarefreeRieszKernel z L f) w‖ =
      ‖squarefreeAnalyticFactor z (1+w)‖ * ‖riemannZeta (1+w)‖^z *
        Real.exp (L*w.re) / (‖1+w‖*‖2+w‖) := by
  have hw1 : (1+w) ≠ 1 := by intro h; apply hw; linear_combination h
  rw [squarefreeRieszKernel_factorization,norm_div,norm_mul,
    squarefreeContourSeries_norm hw1 hf,norm_mul,Complex.norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]

theorem squarefreeRieszKernel_local {z L : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousAt f 1) (h0 : f 1 = 0)
    (he : (fun s => exp (f s)) =ᶠ[𝓝 1] zetaPoleFactor) :
    (fun w => squarefreeRieszKernel z L f w) =ᶠ[𝓝 0]
      (fun w => exp ((L:ℂ)*w) * (squarefreeSingularFactor z (1+w)/(2+w))) := by
  have hshift : Tendsto (fun w : ℂ => 1+w) (𝓝 0) (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_id : Tendsto (fun w : ℂ => 1+w) (𝓝 0) (𝓝 (1+(0:ℂ))))
  filter_upwards [(normalized_log_eq_principal_near hf h0 he).comp_tendsto hshift] with w hw
  change f (1+w) = log (zetaPoleFactor (1+w)) at hw
  simp only [squarefreeRieszKernel,squarefreeSingularFactor,hw,div_eq_mul_inv,mul_inv_rev]
  ring

end JointDickman

end OAI
