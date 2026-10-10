import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayProjection
import OAI.Analysis.BiholderTransport.Coordinates.JointNormalChart
import OAI.Analysis.BiholderTransport.Regularity.SmallAffineTimeTube

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma coordinate_geodesic_affine {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {q : ℝ → E × E} {s t c : ℝ}
    (hq : HasDerivAt q (coordinateGeodesicField g (q (s+c*t))) (s+c*t)) :
    HasDerivAt (fun w => ((q (s+c*w)).1,c • (q (s+c*w)).2))
      (coordinateGeodesicField g ((q (s+c*t)).1,c • (q (s+c*t)).2)) t := by
  have hq₁ : HasDerivAt (fun w => (q w).1) (q (s+c*t)).2 (s+c*t) :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt (s+c*t) hq
  have hq₂ : HasDerivAt (fun w => (q w).2)
      (-coordinateChristoffel g (q (s+c*t)).1 (q (s+c*t)).2 (q (s+c*t)).2) (s+c*t) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt (s+c*t) hq
  have h₁ := hq₁.scomp t (((hasDerivAt_id t).const_mul c).const_add s)
  have h₂ := (hq₂.scomp t (((hasDerivAt_id t).const_mul c).const_add s)).const_smul c
  convert! h₁.prodMk h₂ using 1
  simp only [coordinateGeodesicField,coordinateChristoffel_smul_left,
    coordinateChristoffel_smul_right,mul_one,smul_neg]

variable [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_locally_minimizing (z : TangentBundle 𝓘(ℝ,E) M) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ, |s-t₀| < ε → |u-t₀| < ε →
      dist (sprayFlow s z).1 (sprayFlow u z).1 = |s-u| * ‖z.2‖ := by
  let γ := fun t => sprayFlow t z
  let a := γ t₀
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let cM := extChartAt 𝓘(ℝ,E) a.1
  let q := χ ∘ γ
  have hγ := (sprayFlow_curve z).isMIntegralCurveAt t₀
  have hγc : ContinuousAt (fun t => (γ t).1) t₀ :=
    (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt.comp
      hγ.continuousAt
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,_,hΦ0,hΦode,_,hesub,_,_,hδsrc,hediag,_,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a.1
  have hnear : ∀ᶠ s in 𝓝 t₀, (γ s).1 ∈ Metric.ball a.1 δ :=
    hγc.preimage_mem_nhds (Metric.ball_mem_nhds _ hδ)
  have hode : ∀ᶠ s in 𝓝 t₀,
      (γ s).1 ∈ Metric.ball a.1 δ ∧
      HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q s)) s := by
    filter_upwards [hnear,hγ.eventually_hasDerivAt] with s hs hd
    rw [geodesicSpray_coordinates a (γ s) (hδsrc hs)] at hd
    exact ⟨hs,hd⟩
  obtain ⟨h,hh,hN⟩ := Metric.mem_nhds_iff.mp hode
  have hN' : ∀ s : ℝ, |s-t₀| < h → (γ s).1 ∈ Metric.ball a.1 δ ∧
      HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q s)) s := by
    intro s hs
    exact hN (show s ∈ Metric.ball t₀ h by simpa only [Metric.mem_ball,Real.dist_eq] using hs)
  have hqc : ContinuousAt q t₀ := (spray_chart_hasDerivAt hγ).continuousAt
  let K : ℝ × ℝ → E × E := fun p => ((q p.1).1,((p.2-p.1)/τ) • (q p.1).2)
  have hqp : ContinuousAt (fun p : ℝ × ℝ => q p.1) (t₀,t₀) :=
    ContinuousAt.comp (g := q) (f := (Prod.fst : ℝ × ℝ → ℝ)) hqc continuousAt_fst
  have hscale : ContinuousAt (fun p : ℝ × ℝ => (p.2-p.1)/τ) (t₀,t₀) :=
    (continuousAt_snd.sub continuousAt_fst).div_const τ
  have hK : ContinuousAt K (t₀,t₀) := hqp.fst.prodMk (hscale.smul hqp.snd)
  have hKt : K (t₀,t₀) ∈ e.source := by
    simpa only [K,sub_self,zero_div,zero_smul,q,χ,Function.comp_apply,tangent_chart_apply]
      using hediag a.1 (Metric.mem_ball_self hδ)
  obtain ⟨η,hη,hηK⟩ := Metric.mem_nhds_iff.mp
    (hK.preimage_mem_nhds (e.open_source.mem_nhds hKt))
  obtain ⟨ε,hε,hεη,hεh,htube⟩ := exists_small_affine_time_tube t₀ hh hτ hr hη
  refine ⟨ε,hε,?_⟩
  intro s u hs hu
  have hsN := hN' s (hs.trans_le hεh)
  have huN := hN' u (hu.trans_le hεh)
  let c := (u-s)/τ
  let v₀ : E × E := ((q s).1,c • (q s).2)
  have hv : v₀ ∈ e.source := by
    change K (s,u) ∈ e.source
    apply hηK (a := (s,u))
    simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq] using
      max_lt (hs.trans_le hεη) (hu.trans_le hεη)
  have hvball := hesub hv
  let P : ℝ → E × E := fun w => ((q (s+c*w)).1,c • (q (s+c*w)).2)
  have hPimg : ∀ w ∈ Ioo (-r) r, (P w).1 ∈ cM.target := by
    intro w hw
    have hw' : |w| < r := abs_lt.mpr hw
    have hNw := hN' (s+c*w) (htube s u w hs hu hw')
    exact cM.map_source (hδsrc hNw.1)
  have hPode : ∀ w ∈ Ioo (-r) r,
      HasDerivAt P (coordinateGeodesicField (riemannianCoordinateMetric a.1) (P w)) w := by
    intro w hw
    exact coordinate_geodesic_affine (hN' (s+c*w) (htube s u w hs hu (abs_lt.mpr hw))).2
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have h₁ := sprayFlow_eq_coordinate_curve a hr
    (fun w hw => (hΦode w hw v₀ hvball).1)
    (fun w hw => (hΦode w hw v₀ hvball).2)
    (congrArg χ.symm (hΦ0 v₀ hvball)) ht
  have h₂ := sprayFlow_eq_coordinate_curve a hr hPimg hPode
    (show χ.symm (P 0) = χ.symm v₀ by simp only [P,v₀,mul_zero,add_zero]) ht
  have hEq : Φ (τ,v₀) = P τ := by
    have hh := congrArg χ (h₁.symm.trans h₂)
    rw [χ.right_inv ((tangent_chart_target_iff a _).mpr (hΦode τ ht v₀ hvball).1),
      χ.right_inv ((tangent_chart_target_iff a _).mpr (hPimg τ ht))] at hh
    exact hh
  have htime : s+c*τ = u := by
    dsimp [c]
    rw [div_mul_cancel₀ _ (ne_of_gt hτ)]
    ring
  have hend : (Φ (τ,v₀)).1 = cM (γ u).1 := by
    rw [hEq]
    change (q (s+c*τ)).1 = _
    rw [htime]
    exact congrArg Prod.fst (tangent_chart_apply a (γ u))
  have hmet := hdist (γ s).1 hsN.1 (γ u).1 huN.1 (c • (q s).2) hv hend
  have hen : riemannianCoordinateMetric a.1 (q s).1 (q s).2 (q s).2 = ‖(γ s).2‖^2 :=
    coordinate_spray_energy a (γ s) (hδsrc hsN.1)
  have hsc : riemannianCoordinateMetric a.1 (q s).1 (c • (q s).2) (c • (q s).2) =
      (c*‖(γ s).2‖)^2 := by
    simp only [map_smul,smul_apply,smul_eq_mul,hen]
    ring
  change dist (γ s).1 (γ u).1 = τ * Real.sqrt
    (riemannianCoordinateMetric a.1 (q s).1 (c • (q s).2) (c • (q s).2)) at hmet
  rw [hsc,Real.sqrt_sq_eq_abs,abs_mul,abs_norm] at hmet
  calc
    dist (γ s).1 (γ u).1 = τ * (|c| * ‖(γ s).2‖) := hmet
    _ = |s-u| * ‖(γ s).2‖ := by
      dsimp [c]
      rw [abs_div,abs_of_pos hτ,abs_sub_comm u s]
      field_simp [ne_of_gt hτ]
    _ = |s-u| * ‖z.2‖ := by rw [sprayFlow_speed]

end WeakMTWTransport

end

end OAI
