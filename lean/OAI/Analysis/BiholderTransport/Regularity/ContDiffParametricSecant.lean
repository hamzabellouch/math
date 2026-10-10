import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma contDiffAt_parametric_secant_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E×ℝ → ℝ} {x : E}
    (hF : ContDiffAt ℝ 1 F (x,0)) {K : ℝ}
    (hK : K < fderiv ℝ F (x,0) (0,1)) :
    ∀ᶠ q : E×ℝ in 𝓝 (x,0), 0≤q.2 → K*q.2≤F q-F (q.1,0) := by
  have hd : ContinuousAt (fun q : E×ℝ => fderiv ℝ F q (0,1)) (x,0) :=
    (hF.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have H : ∀ᶠ q : E×ℝ in 𝓝 (x,0), ContDiffAt ℝ 1 F q ∧ K<fderiv ℝ F q (0,1) :=
    (hF.eventually (by norm_num)).and (hd.preimage_mem_nhds (Ioi_mem_nhds hK))
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp H
  obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp hV
  have hnear : U ×ˢ Metric.ball (0:ℝ) δ ∈ 𝓝 (x,0) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hU (Metric.ball_mem_nhds (0:ℝ) hδ)
  filter_upwards [hnear] with q hq ht
  have hqt : q.2<δ := (le_abs_self q.2).trans_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hq.2)
  have Hj : ∀ r∈Icc 0 q.2, ContDiffAt ℝ 1 F (q.1,r) ∧ K<fderiv ℝ F (q.1,r) (0,1) := by
    intro r hr
    exact hUV ⟨hq.1,hδV (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hr.1] using hr.2.trans_lt hqt)⟩
  have hD : ∀ r∈Icc 0 q.2, HasDerivAt (fun r => F (q.1,r))
      (fderiv ℝ F (q.1,r) (0,1)) r := by
    intro r hr
    exact ((Hj r hr).1.differentiableAt_one.hasFDerivAt).comp_hasDerivAt r
      ((hasDerivAt_const r q.1).prodMk (hasDerivAt_id r))
  rcases ht.eq_or_lt with he|ht
  · have hqeq : q = (q.1, 0) := by ext <;> simp [←he]
    rw [hqeq]
    simp
  obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope (fun r => F (q.1,r))
    (fun r => fderiv ℝ F (q.1,r) (0,1)) ht
    (fun r hr => (hD r hr).continuousAt.continuousWithinAt)
    (fun r hr => hD r ⟨hr.1.le,hr.2.le⟩)
  have hk := (Hj r ⟨hr.1.le,hr.2.le⟩).2.le
  rw [he,sub_zero] at hk
  exact (le_div_iff₀ ht).mp hk

end WeakMTWTransport

end

end OAI
