import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicOn
import OAI.Geometry.WeakMTW.Geodesics.LocalGeodesic
import OAI.Geometry.WeakMTW.Coordinates.CoordinateExistence

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open ChartMetric CoordinateGeometry

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
 theorem coordinate_curve_state (x : M) {q : ℝ → E × E} {t : ℝ}
    (ht : (q t).1 ∈ (chartAt E x).target)
    (hq : HasDerivAt q (geodesicSpray (metric x) (q t)) t) :
    curveState (E := E) (fun s => (chartAt E x).symm (q s).1) t =
      ⟨(chartAt E x).symm (q t).1, chartLift x (q t).1 (q t).2⟩ := by
  have hc : HasDerivAt (fun s => (q s).1) (q t).2 t := hq.fst
  have hmc := mdifferentiableAt_iff_differentiableAt.mpr hc.differentiableAt
  have hms := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E)) (chart_mem_atlas E x) ht
  refine TotalSpace.ext ?_ ?_
  · rfl
  apply heq_of_eq
  dsimp only [curveState]
  rw [chartLift_eq_mfderiv_symm x ht]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((chartAt E x).symm ∘ fun s => (q s).1) t 1 = _
  rw [mfderiv_comp t hms hmc]
  simp only [mfderiv_eq_fderiv]
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x).symm (q t).1)
    (fderiv ℝ (fun s : ℝ => (q s).1) t 1) = _
  rw [fderiv_apply_one_eq_deriv, hc.deriv]
  rfl

 theorem coordinate_intrinsic (x : M) {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {q : ℝ → E × E} (hqs : ContDiffOn ℝ ∞ q U)
    (hq : ∀ t ∈ U, (q t).1 ∈ (chartAt E x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t)
    {a : ℝ} (ha : a ∈ U) :
    IsIntrinsicGeodesicOn (E := E) (fun t => (chartAt E x).symm (q t).1)
      (Real.sqrt (metric x (q a).1 (q a).2 (q a).2)) U := by
  refine ⟨contMDiffOn_chart_symm.comp (contMDiffOn_iff_contDiffOn.mpr hqs.fst)
    (fun t ht => (hq t ht).1), ?_⟩
  intro t ht
  obtain ⟨ε, hε, _, hdist⟩ := coordinate_geodesic_locally_minimizes x hU hqs hq ht
  have he := geodesic_energy_on_connected (chartAt E x).open_target
    ((metric_smooth x).differentiableOn (by simp)) (fun z _ => metric_symmetric x z)
    (fun z hz v hv => metric_positive x hz hv) hU hUc hq ht ha
  exact ⟨ε, hε, by simpa only [he] using hdist⟩

 theorem uniformly_local_intrinsic (x : M) {C : ℝ} (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
        ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
          IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Metric.ball 0 ε) := by
  let c := chartAt E x
  let e := trivializationAt E (fun y : M => TangentSpace 𝓘(ℝ, E) y) x
  obtain ⟨ε, hε, W, hW, hxW, hWS, hlocal⟩ := uniform_local_geodesics c.open_target
    (metric_smooth x) (fun z hz v hv => metric_positive x hz hv)
    (c.map_source (mem_chart_source E x)) C
  let V := c.source ∩ c ⁻¹' W
  have hV : IsOpen V := c.continuousOn.isOpen_inter_preimage c.open_source hW
  refine ⟨ε, hε, V, hV, ⟨mem_chart_source E x, hxW⟩, ?_⟩
  intro y hy v hv
  have hyb : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy.1
  let w : E := e.continuousLinearMapAt ℝ y v
  have hinv : chartLift x (c y) w = v := by
    dsimp only [chartLift]
    rw [c.left_inv hy.1]
    exact e.symmL_continuousLinearMapAt hyb v
  have henergy : metric x (c y) w w = ‖v‖ ^ 2 := by
    rw [metric_apply]
    dsimp only [chartLift]
    rw [c.left_inv hy.1]
    change inner ℝ (e.symmL ℝ y w) (e.symmL ℝ y w) = ‖v‖ ^ 2
    rw [e.symmL_continuousLinearMapAt hyb v]
    exact real_inner_self_eq_norm_sq v
  obtain ⟨q, hq₀, hqs, hq⟩ := hlocal (c y) hy.2 w
    (henergy ▸ (sq_le_sq₀ (norm_nonneg v) hC).mpr hv)
  let γ : ℝ → M := fun t => c.symm (q t).1
  have h0 : (0 : ℝ) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hstate := coordinate_curve_state x (hq 0 h0).1 (hq 0 h0).2
  rw [hq₀] at hstate
  have hg := coordinate_intrinsic x Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected hqs hq h0
  rw [hq₀, henergy, Real.sqrt_sq (norm_nonneg v)] at hg
  refine ⟨γ, ?_, hg⟩
  rw [hstate]
  apply TotalSpace.ext (c.left_inv hy.1)
  exact heq_of_eq hinv

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
