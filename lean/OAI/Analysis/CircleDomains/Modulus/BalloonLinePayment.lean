import OAI.Analysis.CircleDomains.Sobolev.SmoothCutoffLinePayment

namespace OAI

/-! The actual smooth balloon cutoffs pay for all unit-speed affine
line segments with their indicator densities. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_affine_line_increment {f g : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ∀ z, ‖fderiv ℝ f z‖ ≤ g z)
    (z e : ℂ) (he : ‖e‖ ≤ 1) {x y : ℝ}
    (hgi : IntervalIntegrable (fun t => g (z+t • e)) volume x y) :
    |f (z+x • e)-f (z+y • e)| ≤ ∫ t in uIoc x y, g (z+t • e) := by
  apply smooth_line_increment_payment (hf.comp (by fun_prop)) hgi
  intro t _
  have hline : HasDerivAt (fun s : ℝ => z+s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add z
  have hder := ((hf.differentiable_one (z+t • e)).hasFDerivAt.comp_hasDerivAt t hline).deriv
  rw [hder,← Real.norm_eq_abs]
  exact ((fderiv ℝ f (z+t • e)).unit_le_opNorm e he).trans (hg _)

 theorem balloon_line_density_intervalIntegrable (c z e : ℂ) (d : ℝ) {C : ℝ}
    (hC : 0 ≤ C) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => (ball c d).indicator (fun _ => C) (z+t • e)) volume x y := by
  have hline : Continuous (fun t : ℝ => z+t • e) := by fun_prop
  have hm : Measurable (fun t : ℝ => (ball c d).indicator (fun _ => C) (z+t • e)) :=
    (measurable_const.indicator (s := ball c d) measurableSet_ball).comp hline.measurable
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume x y).def'.mono'
    hm.aestronglyMeasurable.restrict
  apply Eventually.of_forall
  intro t
  simpa only [Real.norm_of_nonneg hC] using
    norm_indicator_le_norm_self (s := ball c d) (fun _ : ℂ => C) (z+t • e)

 theorem balloon_cutoff_line_payment {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    {c : ℂ} {d C : ℝ} (hC : 0 ≤ C) (hd : 0 < d)
    (hder : ∀ z, ‖fderiv ℝ f z‖ ≤ (ball c d).indicator (fun _ => C/d) z)
    (z e : ℂ) (he : ‖e‖ ≤ 1) (x y : ℝ) :
    |f (z+x • e)-f (z+y • e)| ≤
      ∫ t in uIoc x y, (ball c d).indicator (fun _ => C/d) (z+t • e) :=
  smooth_affine_line_increment hf hder z e he
    (balloon_line_density_intervalIntegrable c z e d (div_nonneg hC hd.le) x y)

end CircleDomainRigidity

end

end OAI
