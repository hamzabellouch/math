import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.FibreNonfocal
import OAI.Geometry.WeakMTW.Variations.ActionHessian
import OAI.Geometry.WeakMTW.Variations.MajorantHessian

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem cost_coord_eq_inverse_arbitrary_chart (x y : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (hy₀ : exp x v ∈ (chartAt (Model n) y).source)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) =
      pairExpCoordinates (n := n) x y)
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source) :
    ∀ᶠ q : Model n × Model n in
      𝓝 (chartAt (Model n) x x,chartAt (Model n) y (exp x v)),
      cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm q.2) =
        metric x (e.symm q).1 (e.symm q).2 (e.symm q).2 / 2 := by
  let c := chartAt (Model n) x
  let d := chartAt (Model n) y
  let a := c x
  let b := d (exp x v)
  have hx : x ∈ c.source := mem_chart_source (Model n) x
  have hy : exp x v ∈ d.source := hy₀
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
    rw [he,pairExpCoordinates_state x y p hpU.1]
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
  convert (show ‖p.2‖^2 = metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 from
    by simpa only [real_inner_self_eq_norm_sq] using hm.symm) using 1
  rfl

 def branchHessianDiag (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (v ξ : TangentSpace (model n) x) : ℝ :=
    fderiv ℝ (fderiv ℝ (branchAction x e)) (chartAt (Model n) x x,chartAt (Model n) y (exp x v))
      (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0) +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v)

 theorem branchHessianDiag_continuous (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {v : TangentSpace (model n) x}
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source)
    (ξ : TangentSpace (model n) x) : ContinuousAt (fun w => branchHessianDiag x y e w ξ) v := by
  have heq : e (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) =
      (chartAt (Model n) x x,chartAt (Model n) y (exp x v)) := by rw [he,pairExpCoordinates_vertical]
  have ht := heq ▸ e.map_source hev
  have hA := ((branchAction_smooth x y e hes hei) _ ht).contDiffAt (e.open_target.mem_nhds ht)
  have hH := (hA.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hy : exp x v ∈ (chartAt (Model n) y).source := by
    have hh := (hes hev).2
    have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
      (stateChart_source x _).mpr (mem_chart_source (Model n) x)
    rw [(stateChart x).left_inv hp] at hh
    have hg : geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source :=
      (stateChart_source y _).mp hh
    simpa only [← exp_eq_geodesic] using hg
  have hq : ContDiffAt ℝ ∞ (fun w => (chartAt (Model n) x x,chartAt (Model n) y (exp x w))) v :=
    contDiffAt_const.prodMk (exp_coordinates_smooth x y hy)
  have hfirst : ContinuousAt (fun w => fderiv ℝ (fderiv ℝ (branchAction x e))
      (chartAt (Model n) x x,chartAt (Model n) y (exp x w))
      (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0)) v :=
    (((hH.comp v hq).clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt
  refine hfirst.add ?_
  unfold lowerChristoffel
  fun_prop

 theorem actionHessian_eq_branch (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hev : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source)
    (ξ : TangentSpace (model n) x) : actionHessian x v ξ ξ = branchHessianDiag x y e v ξ := by
  let a := chartAt (Model n) x x
  let b := chartAt (Model n) y (exp x v)
  let u := tangentChartLinear x ξ
  have hp : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hy : exp x v ∈ (chartAt (Model n) y).source := by
    have hh := (hes hev).2
    rw [(stateChart x).left_inv hp] at hh
    have hg : geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source :=
      (stateChart_source y _).mp hh
    simpa only [← exp_eq_geodesic] using hg
  have heq : e (stateChart x (⟨x,v⟩ : TangentBundle (model n) M)) = (a,b) := by rw [he,pairExpCoordinates_vertical]
  have ht := heq ▸ e.map_source hev
  have hEq : initialCost x (exp x v) =ᶠ[𝓝 a] (fun r => branchAction x e (r,b)) := by
    have hmap : ContinuousAt (fun r : Model n => (r,b)) a := continuousAt_id.prodMk continuousAt_const
    have hh := hmap.tendsto (cost_coord_eq_inverse_arbitrary_chart x y hv hy e he hev)
    filter_upwards [hh] with r hr
    change cost ((chartAt (Model n) x).symm r) ((chartAt (Model n) y).symm b) = _ at hr
    rw [(chartAt (Model n) y).left_inv hy] at hr
    exact hr
  have hH : fderiv ℝ (fderiv ℝ (initialCost x (exp x v))) a =
      fderiv ℝ (fderiv ℝ (fun r => branchAction x e (r,b))) a := hEq.fderiv.fderiv_eq
  let L : Model n →L[ℝ] Model n × Model n := (ContinuousLinearMap.id ℝ (Model n)).prod 0
  let c : Model n × Model n := (0,b)
  have hA := ((branchAction_smooth x y e hes hei) _ ht).contDiffAt (e.open_target.mem_nhds ht)
  have hA' : ContDiffAt ℝ 2 (branchAction x e) (c+L a) := by
    simpa only [c,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply,
      Prod.mk_add_mk,zero_add,add_zero] using hA.of_le (by simp)
  have hc := hessian_affine_pullback L c hA' u
  have hc' : fderiv ℝ (fderiv ℝ (fun r => branchAction x e (r,b))) a u u =
      fderiv ℝ (fderiv ℝ (branchAction x e)) (a,b) (u,0) (u,0) := by
    simpa only [c,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply,
      Prod.mk_add_mk,zero_add,add_zero] using hc
  change fderiv ℝ (fderiv ℝ (initialCost x (exp x v))) a u u + _ =
    fderiv ℝ (fderiv ℝ (branchAction x e)) (a,b) (u,0) (u,0) + _
  rw [hH,hc']
  rfl

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
