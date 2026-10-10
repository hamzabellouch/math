import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledParameterBound
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! Uniform fixed-power continuity of the nonlinear inner amplitudes. -/

open Set Filter
namespace DefocusingNLS

theorem radial_coupled_parameter_limit (P : RadialInnerData) (Pn : ℕ → RadialInnerData)
    (hp : ∀ i, (Pn i).p=P.p) (hR : ∀ i, (Pn i).R=P.R)
    (hlo : Tendsto (fun i => (Pn i).lo) atTop (nhds P.lo))
    (hc : Tendsto (fun i => (Pn i).c) atTop (nhds P.c))
    (hb : Tendsto (fun i => (Pn i).b) atTop (nhds P.b))
    (H : ℝ → ℝ) (Hn : ℕ → ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H)
    (hHn : ∀ i, RadialInnerOutputSpec (Pn i).p (Pn i).R (Pn i).lo (Pn i).c (Pn i).b (Hn i) (Hn i)) :
    TendstoUniformlyOn Hn H atTop (Icc 0 P.R) := by
  have hlim : Tendsto (fun i => 3*|P.lo-(Pn i).lo|+|P.c-(Pn i).c|+|P.b-(Pn i).b|)
      atTop (nhds 0) := by
    have hh := (((hlo.const_sub P.lo).abs.const_mul 3).add
      (hc.const_sub P.c).abs).add (hb.const_sub P.b).abs
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using hh
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi r hr
  have he := radial_coupled_parameter_bound P (Pn i) (hp i) (hR i) H (Hn i) hH (hHn i) r hr
  simpa only [Real.dist_eq] using he.trans_lt hi

end DefocusingNLS

end OAI
