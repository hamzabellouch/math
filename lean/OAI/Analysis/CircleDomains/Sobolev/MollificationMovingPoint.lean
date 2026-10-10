import OAI.Analysis.CircleDomains.Sobolev.UniformLocalMollification

namespace OAI

/-! The actual positive mollifiers converge at moving points whenever
those points converge. Only continuity near a compact ball is used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma planarMollification_tendsto_moving
    {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {x : ℕ → EuclideanPlane} {y : EuclideanPlane}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => planarMollification u n (x n)) atTop (𝓝 (u y)) := by
  have herr : Tendsto (fun n => planarMollification u n (x n)-u (x n)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hm := planarMollification_uniform_on_compact hu.aestronglyMeasurable
      (isCompact_closedBall y 1) isOpen_univ (subset_univ _) hu.continuousOn hε
    have hb : ∀ᶠ n in atTop, x n ∈ closedBall y 1 :=
      (hx.eventually (Metric.ball_mem_nhds y zero_lt_one)).mono fun _ h => ball_subset_closedBall h
    filter_upwards [hm, hb] with n hn hb
    simpa only [dist_zero_right, Real.norm_eq_abs] using hn (x n) hb
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using herr.add (hu.continuousAt.tendsto.comp hx)

end CircleDomainRigidity

end

end OAI
