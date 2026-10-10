import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.PairExpCoordinates
import OAI.Geometry.WeakMTW.Geodesics.HopfRinow
import OAI.Geometry.WeakMTW.Geodesics.BundleMinimizerCompactness

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem pairExpCoordinates_state (x y : M) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) :
    pairExpCoordinates (n := n) x y (stateChart x p) =
      (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) := by
  dsimp only [pairExpCoordinates]
  rw [(stateChart x).left_inv hp]
  change (_,chartAt (Model n) y (geodesic p 1)) = _
  rw [← exp_eq_geodesic]
  rfl

 theorem cost_coord_eq_interior_inverse (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) =
      pairExpCoordinates (n := n) x (exp x v))
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source) :
    ∀ᶠ q : Model n × Model n in
      𝓝 (chartAt (Model n) x x,chartAt (Model n) (exp x v) (exp x v)),
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) (exp x v)).symm q.2) =
        metric x (e.symm q).1 (e.symm q).2 (e.symm q).2 / 2 := by
  let c := chartAt (Model n) x
  let d := chartAt (Model n) (exp x v)
  let a := c x
  let b := d (exp x v)
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hy : exp x v ∈ d.source := mem_chart_source (Model n) (exp x v)
  have ha : a ∈ c.target := c.map_source hx
  have hb : b ∈ d.target := d.map_source hy
  have hvS : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr hx
  let U := (stateChart x).source ∩ stateChart x ⁻¹' e.source
  have hU : IsOpen U :=
    (stateChart x).continuousOn.isOpen_inter_preimage (stateChart x).open_source e.open_source
  have hvU : (⟨x,v⟩ : TangentBundle (model n) M) ∈ U := ⟨hvS,hev⟩
  have hnear := minimizing_states_near_unique x hv hU hvU
  have hpair : Tendsto (fun q : Model n × Model n => (c.symm q.1,d.symm q.2))
      (𝓝 (a,b)) (𝓝 (x,exp x v)) := by
    have hc := ContinuousAt.comp (x := (a,b)) (f := Prod.fst) (g := c.symm)
      (c.symm.continuousAt ha) (continuousAt_fst : ContinuousAt (fun q : Model n × Model n => q.1) (a,b))
    have hd := ContinuousAt.comp (x := (a,b)) (f := Prod.snd) (g := d.symm)
      (d.symm.continuousAt hb) (continuousAt_snd : ContinuousAt (fun q : Model n × Model n => q.2) (a,b))
    simpa only [Function.comp_def,Prod.fst,Prod.snd,a,b,c.left_inv hx,d.left_inv hy] using (hc.prodMk hd).tendsto
  have hqt : ∀ᶠ q : Model n × Model n in 𝓝 (a,b), q.1 ∈ c.target ∧ q.2 ∈ d.target :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (c.open_target.mem_nhds ha))
      (continuousAt_snd.preimage_mem_nhds (d.open_target.mem_nhds hb))
  filter_upwards [hpair hnear,hqt] with q hq hqt
  obtain ⟨w,hew,hnw⟩ := exists_minimizing_vector (n := n) (c.symm q.1) (d.symm q.2)
  let p : TangentBundle (model n) M := ⟨c.symm q.1,w⟩
  have hpM : p ∈ totalMinimizingSet := by
    change dist (c.symm q.1) (exp (c.symm q.1) w) = ‖w‖
    rw [hew,hnw]
  have hpE : baseExp p = (c.symm q.1,d.symm q.2) := Prod.ext rfl hew
  have hpU : p ∈ U := hq p hpM hpE
  have heq : e (stateChart x p) = q := by
    rw [he,pairExpCoordinates_state x (exp x v) p hpU.1]
    change (c (c.symm q.1),d (exp (c.symm q.1) w)) = q
    rw [hew,c.right_inv hqt.1,d.right_inv hqt.2]
  have hlog : e.symm q = stateChart x p := by
    rw [← heq,e.left_inv hpU.2]
  rw [hlog]
  have hpS : p.1 ∈ c.source := (stateChart_source x _).mp hpU.1
  have hm := stateChart_pairing x p.1 hpS p.2 p.2
  dsimp only [cost]
  rw [← hnw]
  congr 1
  exact (show ‖p.2‖^2 = metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 from
    by simpa only [real_inner_self_eq_norm_sq] using hm.symm)

 theorem cost_coord_smooth_interior (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (fun q : Model n × Model n =>
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) (exp x v)).symm q.2))
      (chartAt (Model n) x x,chartAt (Model n) (exp x v) (exp x v)) := by
  let y := exp x v
  let q := (chartAt (Model n) x x,chartAt (Model n) y y)
  obtain ⟨e,he,hev,hes,hei⟩ := pairExpCoordinates_local_inverse x y hv (mem_chart_source (Model n) y)
  have heq : e (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) = q := by
    rw [he,pairExpCoordinates_vertical]
  have hq : q ∈ e.target := heq ▸ e.map_source hev
  have hν : ContDiffAt ℝ ∞ e.symm q := (hei q hq).contDiffAt (e.open_target.mem_nhds hq)
  have hνT : (e.symm q).1 ∈ (chartAt (Model n) x).target :=
    (stateChart_target x _).mp (hes (e.map_target hq)).1
  have hG : ContDiffAt ℝ ∞ (fun p : Model n × Model n => metric x (e.symm p).1) q :=
    ContDiffAt.comp (f := fun p => (e.symm p).1) (g := metric x) q
      ((metric_smooth x _ hνT).contDiffAt ((chartAt (Model n) x).open_target.mem_nhds hνT)) hν.fst
  have hs : ContDiffAt ℝ ∞ (fun p : Model n × Model n =>
      metric x (e.symm p).1 (e.symm p).2 (e.symm p).2 / 2) q :=
    ((hG.clm_apply hν.snd).clm_apply hν.snd).div_const 2
  exact hs.congr_of_eventuallyEq (cost_coord_eq_interior_inverse x hv e he hev)

 theorem cost_smooth_at_injectivity (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) :
    ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M × M => cost q.1 q.2) (x,exp x v) := by
  let y := exp x v
  let c := chartAt (Model n) x
  let d := chartAt (Model n) y
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hy : y ∈ d.source := mem_chart_source (Model n) y
  have hc : ContMDiffAt (model n) 𝓘(ℝ, Model n) ∞ c x :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hx)
  have hd : ContMDiffAt (model n) 𝓘(ℝ, Model n) ∞ d y :=
    contMDiffOn_chart.contMDiffAt (d.open_source.mem_nhds hy)
  have hp : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
      (fun q : M × M => (c q.1,d q.2)) (x,y) :=
    (contMDiffAt_prod_module_iff _).mpr ⟨ContMDiffAt.comp (f := Prod.fst) (g := c) (x,y) hc contMDiffAt_fst,
      ContMDiffAt.comp (f := Prod.snd) (g := d) (x,y) hd contMDiffAt_snd⟩
  have hh := ContMDiffAt.comp (f := fun q : M × M => (c q.1,d q.2))
    (g := fun q : Model n × Model n => cost (c.symm q.1) (d.symm q.2))
    (x,y) (contMDiffAt_iff_contDiffAt.mpr (cost_coord_smooth_interior x hv)) hp
  apply hh.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : M × M in 𝓝 (x,y), q.1 ∈ c.source ∧ q.2 ∈ d.source :=
    inter_mem (continuousAt_fst.preimage_mem_nhds (c.open_source.mem_nhds hx))
      (continuousAt_snd.preimage_mem_nhds (d.open_source.mem_nhds hy))
  filter_upwards [hnear] with q hq
  simp only [Function.comp_def,c.left_inv hq.1,d.left_inv hq.2]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
