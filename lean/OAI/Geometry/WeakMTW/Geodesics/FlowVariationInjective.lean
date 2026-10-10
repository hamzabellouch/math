import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.FanCoordinates

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

 theorem chart_flow_smooth (x b : M) (t : ℝ) {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hb : geodesicFlow t ((stateChart x).symm q) ∈ (stateChart b).source) :
    ContDiffAt ℝ ∞ (fun r => stateChart b (geodesicFlow t ((stateChart x).symm r))) q := by
  have hs : ContMDiffOn 𝓘(ℝ, Model n × Model n) ((model n).prod (model n)) ∞
      (stateChart x).symm (stateChart (E := Model n) x).target :=
    by
      rw [modelWithCornersSelf_prod]
      exact contMDiffOn_chart_symm (I := (model n).prod (model n))
        (x := (⟨x,0⟩ : TangentBundle (model n) M))
  have hch : ContMDiffOn ((model n).prod (model n)) 𝓘(ℝ, Model n × Model n) ∞
      (stateChart b) (stateChart (E := Model n) b).source :=
    contMDiffOn_extChartAt (I := (model n).prod (model n))
      (x := (⟨b,0⟩ : TangentBundle (model n) M))
  exact contMDiffAt_iff_contDiffAt.mp
    (((hch _ hb).contMDiffAt ((stateChart b).open_source.mem_nhds hb)).comp q
      (((geodesicFlow_smooth_fixed t) _).comp q
        ((hs _ hq).contMDiffAt ((stateChart x).open_target.mem_nhds hq))))

 theorem fan_zero_state_derivative (x b : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (hx : (1,0) ∈ fanDomain x P) (hb : P 0 ∈ (stateChart b).source)
    (hc : HasDerivAt (fun s => fanCoordinates x P (1,s)) 0 0) :
    HasDerivAt (fun s => stateChart b (P s)) 0 0 := by
  let q₀ := fanCoordinates x P (1,0)
  have hq : q₀ ∈ (stateChart x).target := (stateChart x).map_source hx
  have hback : geodesicFlow (-1) ((stateChart x).symm q₀) = P 0 := by
    change geodesicFlow (-1) ((stateChart x).symm (stateChart x (geodesicFlow 1 (P 0)))) = _
    have hx' : geodesicFlow 1 (P 0) ∈ (stateChart x).source := hx
    rw [(stateChart x).left_inv hx',← geodesicFlow_add]
    norm_num only [neg_add_cancel,geodesicFlow_zero]
  have hT := chart_flow_smooth x b (-1) hq (hback ▸ hb)
  have hcomp := (hT.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), (1,s) ∈ fanDomain x P :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds ((fanDomain_open x hP).mem_nhds hx)
  have he : (fun s => stateChart b (P s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => stateChart b (geodesicFlow (-1) ((stateChart x).symm r))) ∘
        (fun s => fanCoordinates x P (1,s)) := by
    filter_upwards [hnear] with s hs
    change stateChart b (P s) = stateChart b (geodesicFlow (-1)
      ((stateChart x).symm (stateChart x (geodesicFlow 1 (P s)))))
    have hs' : geodesicFlow 1 (P s) ∈ (stateChart x).source := hs
    rw [(stateChart x).left_inv hs',← geodesicFlow_add]
    norm_num only [neg_add_cancel,geodesicFlow_zero]
  simpa only [map_zero] using hcomp.congr_of_eventuallyEq he

omit [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem stateChart_vertical (b : M) (v : TangentSpace (model n) b) :
    stateChart b (⟨b,v⟩ : TangentBundle (model n) M) =
      (chartAt (Model n) b b,
        (trivializationAt (Model n) (TangentSpace (model n)) b).continuousLinearMapAt ℝ b v) := by
  let e := trivializationAt (Model n) (TangentSpace (model n)) b
  apply Prod.ext
  · rfl
  change (e (⟨b,v⟩ : TangentBundle (model n) M)).2 = e.continuousLinearMapAt ℝ b v
  exact (e.continuousLinearMapAt_apply_of_mem ℝ
    (mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) b) v).symm

omit [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem vertical_zero_state_derivative (b : M) (v w : TangentSpace (model n) b)
    (h : HasDerivAt (fun s : ℝ => stateChart b (⟨b,v+s•w⟩ : TangentBundle (model n) M)) 0 0) :
    w = 0 := by
  let e := trivializationAt (Model n) (TangentSpace (model n)) b
  let L := e.continuousLinearMapAt ℝ b
  have he : (fun s : ℝ => stateChart b (⟨b,v+s•w⟩ : TangentBundle (model n) M)) =
      fun s : ℝ => (chartAt (Model n) b b,L v+s•L w) := by
    funext s
    rw [stateChart_vertical,map_add,map_smul]
  rw [he] at h
  have hv : HasDerivAt (fun s : ℝ => L v+s•L w) (L w) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (L v)).add ((hasDerivAt_id (0 : ℝ)).smul_const (L w)) using 1 <;> (first | rfl | simp)
  have hs₀ := (ContinuousLinearMap.snd ℝ (Model n) (Model n)).hasFDerivAt.comp_hasDerivAt 0 h
  have hs : HasDerivAt (fun s : ℝ => L v+s•L w) 0 0 := hs₀
  have hh := hs.unique hv
  have hLw : L w = 0 := hh.symm
  have hpair := stateChart_pairing b b (mem_chart_source (Model n) b) w w
  simp only [stateChart_vertical] at hpair
  change metric b (chartAt (Model n) b b) (L w) (L w) = inner ℝ w w at hpair
  simp only [hLw,map_zero,real_inner_self_eq_norm_sq] at hpair
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hpair.symm)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
