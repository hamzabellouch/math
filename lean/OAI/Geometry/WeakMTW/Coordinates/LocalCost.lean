import Mathlib
import OAI.Geometry.WeakMTW.Model
import OAI.Geometry.WeakMTW.Coordinates.PairNormalDistance

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem cost_coord_eq_normal (x z : M) (hz : z ∈ (chartAt (Model n) x).source)
    (N : NormalFlow (metric x) (chartAt (Model n) x).target (chartAt (Model n) x z)) :
    ∀ᶠ q : Model n × Model n in 𝓝 (chartAt (Model n) x z,chartAt (Model n) x z),
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) x).symm q.2) =
        N.time^2 / 2 * metric x q.1 (N.normal.symm q).2 (N.normal.symm q).2 := by
  let c := chartAt (Model n) x
  let a := c z
  have ha : a ∈ c.target := c.map_source hz
  have hpair : Tendsto (fun q : Model n × Model n => (c.symm q.1,c.symm q.2)) (𝓝 (a,a)) (𝓝 (z,z)) := by
    simpa only [Function.comp_def,a,c.left_inv hz] using
      ((ContinuousAt.comp (x := (a,a)) (f := Prod.fst) (g := c.symm) (c.symm.continuousAt ha) (continuousAt_fst : ContinuousAt (fun q : Model n × Model n => q.1) (a,a))).prodMk
        (ContinuousAt.comp (x := (a,a)) (f := Prod.snd) (g := c.symm) (c.symm.continuousAt ha) (continuousAt_snd : ContinuousAt (fun q : Model n × Model n => q.2) (a,a)))).tendsto
  have heq' : ∀ᶠ q : Model n × Model n in 𝓝 (a,a),
      dist (c.symm q.1) (c.symm q.2) = N.time *
        Real.sqrt (metric x (c (c.symm q.1))
          (N.normal.symm (c (c.symm q.1),c (c.symm q.2))).2
          (N.normal.symm (c (c.symm q.1),c (c.symm q.2))).2) :=
    hpair (eventually_dist_normal_pair x z hz N)
  have hnear : ∀ᶠ q : Model n × Model n in 𝓝 (a,a), q.1 ∈ c.target ∧ q.2 ∈ c.target :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (c.open_target.mem_nhds ha))
      (continuousAt_snd.preimage_mem_nhds (c.open_target.mem_nhds ha))
  filter_upwards [heq',hnear] with q hq hqt
  rw [c.right_inv hqt.1,c.right_inv hqt.2] at hq
  have hnonneg : 0 ≤ metric x q.1 (N.normal.symm q).2 (N.normal.symm q).2 := by
    rw [metric_apply,real_inner_self_eq_norm_sq]
    positivity
  dsimp only [cost]
  rw [hq,mul_pow,Real.sq_sqrt hnonneg]
  ring

 theorem cost_coord_smooth_diag (x z : M) (hz : z ∈ (chartAt (Model n) x).source) :
    ContDiffAt ℝ ∞ (fun q : Model n × Model n =>
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) x).symm q.2)) (chartAt (Model n) x z,chartAt (Model n) x z) := by
  let c := chartAt (Model n) x
  let a := c z
  have ha : a ∈ c.target := c.map_source hz
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) ha
  have he := N.normal_zero c.open_target (metric_smooth x)
    (fun y hy v hv => metric_positive x hy hv) N.center_mem
  have ht : (a,a) ∈ N.normal.target := he ▸ N.normal.map_source N.center_mem
  have hν : ContDiffAt ℝ ∞ (fun q : Model n × Model n => (N.normal.symm q).2) (a,a) :=
    ((N.inverse_smooth _ ht).contDiffAt (N.normal.open_target.mem_nhds ht)).snd
  have hG : ContDiffAt ℝ ∞ (fun q : Model n × Model n => metric x q.1) (a,a) :=
    ContDiffAt.comp (f := Prod.fst) (g := metric x) (a,a)
      ((metric_smooth x a ha).contDiffAt (c.open_target.mem_nhds ha)) contDiffAt_fst
  have hs : ContDiffAt ℝ ∞ (fun q : Model n × Model n =>
      N.time^2 / 2 * metric x q.1 (N.normal.symm q).2 (N.normal.symm q).2) (a,a) :=
    contDiffAt_const.mul ((hG.clm_apply hν).clm_apply hν)
  exact hs.congr_of_eventuallyEq (cost_coord_eq_normal x z hz N)

 theorem cost_smooth_diag (x : M) :
    ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ, ℝ) ∞
      (fun q : M × M => cost q.1 q.2) (x,x) := by
  let c := chartAt (Model n) x
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hc : ContMDiffAt (model n) 𝓘(ℝ, Model n) ∞ c x :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hx)
  have hp : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
      (fun q : M × M => (c q.1,c q.2)) (x,x) :=
    (contMDiffAt_prod_module_iff _).mpr ⟨ContMDiffAt.comp (f := Prod.fst) (g := c) (x,x) hc contMDiffAt_fst,
      ContMDiffAt.comp (f := Prod.snd) (g := c) (x,x) hc contMDiffAt_snd⟩
  have hh := ContMDiffAt.comp
    (f := fun q : M × M => (c q.1,c q.2))
    (g := fun q : Model n × Model n => cost (c.symm q.1) (c.symm q.2))
    (x,x) (contMDiffAt_iff_contDiffAt.mpr (cost_coord_smooth_diag x x hx)) hp
  apply hh.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : M × M in 𝓝 (x,x), q.1 ∈ c.source ∧ q.2 ∈ c.source :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (c.open_source.mem_nhds hx))
      (continuousAt_snd.preimage_mem_nhds (c.open_source.mem_nhds hx))
  filter_upwards [hnear] with q hq
  simp only [Function.comp_def,c.left_inv hq.1,c.left_inv hq.2]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
