import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.ChartPairing
import OAI.Geometry.WeakMTW.Geodesics.GlobalFlow
import OAI.Geometry.WeakMTW.Geodesics.InjectivityUniqueness

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

omit [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem tangent_norm_continuous : Continuous (fun p : TangentBundle (model n) M => ‖p.2‖) := by
  have hh : ContMDiff ((model n).prod 𝓘(ℝ, Model n)) 𝓘(ℝ,ℝ) ∞
      (fun p : TangentBundle (model n) M => inner ℝ p.2 p.2) :=
    (show ContMDiff ((model n).prod 𝓘(ℝ, Model n)) ((model n).prod 𝓘(ℝ, Model n)) ∞
      (fun p : TangentBundle (model n) M => (⟨p.1,p.2⟩ : TangentBundle (model n) M)) from contMDiff_id).inner_bundle contMDiff_id
  simpa only [real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)] using hh.continuous.sqrt

omit [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem locally_compact_tangent_bound (x : M) (R : ℝ) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ K : Set (TangentBundle (model n) M),
      IsCompact K ∧ ∀ p : TangentBundle (model n) M, p.1 ∈ V → ‖p.2‖ ≤ R → p ∈ K := by
  let C := chartAt (Model n) x
  have hx : C x ∈ C.target := C.map_source (mem_chart_source (Model n) x)
  obtain ⟨κ,hκ,W,hW,hWx,hWT,hcoer⟩ := uniform_metric_coercive C.open_target
    (metric_smooth x).continuousOn hx (fun v hv => metric_positive x hx hv)
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hWx)
  let B := Metric.closedBall (C x) (r/2)
  have hBW : B ⊆ W := fun z hz => hrW (lt_of_le_of_lt hz (half_lt_self hr))
  let A : ℝ := 1+R^2/κ
  let Q := B ×ˢ Metric.closedBall (0 : Model n) A
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hQT : Q ⊆ (stateChart x).target := fun q hq => (stateChart_target x q).mpr (hWT (hBW hq.1))
  let K := (stateChart x).symm '' Q
  have hK : IsCompact K := hQ.image_of_continuousOn ((stateChart x).continuousOn_symm.mono hQT)
  let V := C.source ∩ C ⁻¹' Metric.ball (C x) (r/2)
  have hV : IsOpen V := C.continuousOn.isOpen_inter_preimage C.open_source Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_chart_source (Model n) x,Metric.mem_ball_self (half_pos hr)⟩
  refine ⟨V,hV,hxV,K,hK,?_⟩
  intro p hp hpR
  have hpS : p ∈ (stateChart x).source := (stateChart_source x _).mpr hp.1
  let q := stateChart x p
  have hqB : q.1 ∈ B := (show dist (C p.1) (C x) < r/2 from hp.2).le
  have hpair := stateChart_pairing x p.1 hp.1 p.2 p.2
  have hco := hcoer q.1 (hBW hqB) q.2
  have henergy : metric x q.1 q.2 q.2 = ‖p.2‖^2 := by
    change metric x q.1 q.2 q.2 = inner ℝ p.2 p.2 at hpair
    simpa only [real_inner_self_eq_norm_sq] using hpair
  rw [henergy] at hco
  have hnorm : ‖q.2‖^2 ≤ R^2/κ := (le_div_iff₀ hκ).mpr (by
    have hpR' : ‖p.2‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hpR 2
    nlinarith)
  have hbound : ‖q.2‖ ≤ A := by dsimp only [A]; nlinarith [sq_nonneg (‖q.2‖-1)]
  refine ⟨q,⟨hqB,?_⟩,(stateChart x).left_inv hpS⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using hbound

 def totalMinimizingSet : Set (TangentBundle (model n) M) :=
  {p | dist p.1 (exp p.1 p.2) = ‖p.2‖}

 def baseExp (p : TangentBundle (model n) M) : M × M := (p.1,exp p.1 p.2)

 theorem baseExp_continuous : Continuous (baseExp (n := n) (M := M)) :=
  (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.prodMk exp_total_smooth.continuous

 theorem totalMinimizingSet_closed : IsClosed (totalMinimizingSet (n := n) (M := M)) :=
  isClosed_eq ((contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.dist exp_total_smooth.continuous)
    tangent_norm_continuous

 theorem minimizing_states_near_unique (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) {U : Set (TangentBundle (model n) M)}
    (hU : IsOpen U) (hvU : (⟨x,v⟩ : TangentBundle (model n) M) ∈ U) :
    ∀ᶠ xy : M × M in 𝓝 (x,exp x v), ∀ p ∈ totalMinimizingSet,
      baseExp p = xy → p ∈ U := by
  obtain ⟨V,hV,hxV,K,hK,hbound⟩ := locally_compact_tangent_bound (n := n) x (Metric.diam (univ : Set M))
  let L := (K ∩ totalMinimizingSet (n := n) (M := M)) \ U
  have hL : IsCompact L := (hK.inter_right totalMinimizingSet_closed).diff hU
  have hC := (hL.image baseExp_continuous).isClosed
  have hnot : (x,exp x v) ∉ baseExp '' L := by
    rintro ⟨⟨b,w⟩,hw,he⟩
    have hb : b = x := congrArg Prod.fst he
    subst b
    have hex : exp x w = exp x v := congrArg Prod.snd he
    have hm : w ∈ minimizingDomain x := hw.1.2
    have hh := minimizing_vector_unique_of_injectivity hv hm hex.symm
    exact hw.2 (by simpa only [← hh] using hvU)
  have hVp : ∀ᶠ xy : M × M in 𝓝 (x,exp x v), xy.1 ∈ V :=
    continuousAt_fst.preimage_mem_nhds (hV.mem_nhds hxV)
  filter_upwards [hC.isOpen_compl.mem_nhds hnot,hVp] with xy hxy hVxy
  intro p hp he
  have hpn : ‖p.2‖ ≤ Metric.diam (univ : Set M) := by
    rw [← show dist p.1 (exp p.1 p.2) = ‖p.2‖ from hp]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have hpV : p.1 ∈ V := by simpa only [← he,baseExp] using hVxy
  have hpK := hbound p hpV hpn
  by_contra hn
  exact hxy ⟨p,⟨⟨hpK,hp⟩,hn⟩,he⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
