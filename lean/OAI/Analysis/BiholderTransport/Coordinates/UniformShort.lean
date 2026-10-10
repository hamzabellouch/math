import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayDistanceBound

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma contMDiff_tangentScale :
    ContMDiff (𝓘(ℝ,ℝ).prod (𝓘(ℝ,E).prod 𝓘(ℝ,E))) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun p : ℝ × TangentBundle 𝓘(ℝ,E) M => tangentScale p.1 p.2) := by
  intro p
  have hpr : ContMDiffAt (𝓘(ℝ,ℝ).prod (𝓘(ℝ,E).prod 𝓘(ℝ,E)))
      (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ (fun q : ℝ × TangentBundle 𝓘(ℝ,E) M => q.2) p :=
    contMDiffAt_snd
  rw [Bundle.contMDiffAt_totalSpace] at hpr ⊢
  refine ⟨hpr.1,?_⟩
  let e := trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) p.2.1
  have hnear : ∀ᶠ q : ℝ × TangentBundle 𝓘(ℝ,E) M in 𝓝 p, q.2.1 ∈ e.baseSet :=
    hpr.1.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ p.2.1))
  apply (contMDiffAt_fst.smul hpr.2).congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  exact (e.linear ℝ hq).map_smul q.1 q.2.2

lemma sprayFlow_zero_velocity_base (a : M) (t : ℝ) :
    (sprayFlow t (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = a := by
  have hh := dist_sprayFlow_le (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) 0 t
  exact (show a = (sprayFlow t ⟨a,0⟩).1 by
    simpa only [sprayFlow_zero,norm_zero,mul_zero,dist_le_zero] using hh).symm

lemma sprayFlow_minimizing_near_zero_section (a : M) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ z : TangentBundle 𝓘(ℝ,E) M in 𝓝 ⟨a,0⟩,
      dist z.1 (sprayFlow τ z).1 = τ * ‖z.2‖ := by
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,hode,he,hesub,hed,hei,hsrc,hdiag,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  let A : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
  let c := extChartAt 𝓘(ℝ,E) a
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) A
  have hchart0 : χ A = (c a,0) := by
    rw [tangent_chart_apply]
    change (c a,tangentCoordChange 𝓘(ℝ,E) a a a 0) = (c a,0)
    rw [tangentCoordChange_self (mem_extChartAt_source a)]
  have hbase : ContinuousAt (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) A :=
    (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt
  have hflow₀ : Continuous (fun z : TangentBundle 𝓘(ℝ,E) M => sprayFlow τ z) :=
    contMDiff_sprayFlow.continuous.comp (continuous_const.prodMk continuous_id)
  have hflow : ContinuousAt (fun z : TangentBundle 𝓘(ℝ,E) M => (sprayFlow τ z).1) A :=
    (FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt.comp
      hflow₀.continuousAt
  have hnear₁ : ∀ᶠ z in 𝓝 A, z.1 ∈ Metric.ball a δ :=
    hbase.preimage_mem_nhds (Metric.ball_mem_nhds a hδ)
  have hnear₂ : ∀ᶠ z in 𝓝 A, (sprayFlow τ z).1 ∈ Metric.ball a δ :=
    hflow.preimage_mem_nhds (by rw [sprayFlow_zero_velocity_base]; exact Metric.ball_mem_nhds a hδ)
  have hnear₃ : ∀ᶠ z in 𝓝 A, χ z ∈ e.source :=
    (continuousAt_extChartAt A).preimage_mem_nhds
      (e.open_source.mem_nhds (hchart0 ▸ hdiag a (Metric.mem_ball_self hδ)))
  refine ⟨τ,hτ,?_⟩
  filter_upwards [hnear₁,hnear₂,hnear₃] with z hz hy hez
  have hzsrc : z ∈ χ.source := (tangent_chart_source_iff A z).mpr (hsrc hz)
  have hball := hesub hez
  have h₀ : χ.symm (Φ (0,χ z)) = z := by rw [hΦ0 _ hball,χ.left_inv hzsrc]
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have hex := sprayFlow_eq_coordinate_curve A hr
    (fun t ht => (hode t ht (χ z) hball).1)
    (fun t ht => (hode t ht (χ z) hball).2) h₀ ht
  have hchart : χ (sprayFlow τ z) = Φ (τ,χ z) := by
    rw [hex,χ.right_inv ((tangent_chart_target_iff A _).mpr (hode τ ht (χ z) hball).1)]
  have hmet := hdist z.1 hz (sprayFlow τ z).1 hy (χ z).2
  have hcz : (c z.1,(χ z).2) = χ z := by
    exact Prod.ext (congrArg Prod.fst (tangent_chart_apply A z)).symm rfl
  rw [hcz] at hmet
  have hend : (Φ (τ,χ z)).1 = c (sprayFlow τ z).1 := by
    rw [←hchart]; exact congrArg Prod.fst (tangent_chart_apply A _)
  have hh := hmet hez hend
  have hen := coordinate_spray_energy A z (hsrc hz)
  have hfst : (χ z).1 = c z.1 := congrArg Prod.fst (tangent_chart_apply A z)
  rw [hfst] at hen
  rw [hen,Real.sqrt_sq (norm_nonneg _)] at hh
  exact hh

lemma sprayFlow_uniformly_short_minimizing (z₀ : TangentBundle 𝓘(ℝ,E) M) :
    ∀ᶠ p : ℝ × TangentBundle 𝓘(ℝ,E) M in 𝓝 (0,z₀),
      dist p.2.1 (sprayFlow p.1 p.2).1 = |p.1| * ‖p.2.2‖ := by
  obtain ⟨τ,hτ,H⟩ := sprayFlow_minimizing_near_zero_section (E := E) z₀.1
  let S : ℝ × TangentBundle 𝓘(ℝ,E) M → TangentBundle 𝓘(ℝ,E) M :=
    fun p => tangentScale (p.1/τ) p.2
  have hS : ContinuousAt S (0,z₀) :=
    contMDiff_tangentScale.continuous.continuousAt.comp
      ((continuousAt_fst.div_const τ).prodMk continuousAt_snd)
  have hS0 : S (0,z₀) = ⟨z₀.1,0⟩ := by simp [S,tangentScale]
  have hnear := (show Tendsto S (𝓝 (0,z₀)) (𝓝 ⟨z₀.1,0⟩) by
    simpa only [ContinuousAt,hS0] using hS).eventually H
  filter_upwards [hnear] with p hp
  change dist p.2.1 (sprayFlow τ (tangentScale (p.1/τ) p.2)).1 =
    τ * ‖(p.1/τ) • p.2.2‖ at hp
  rw [sprayFlow_scale,div_mul_cancel₀ _ hτ.ne'] at hp
  change dist p.2.1 (sprayFlow p.1 p.2).1 = τ * ‖(p.1/τ) • p.2.2‖ at hp
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos hτ] at hp
  rw [hp, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hτ)]

end WeakMTWTransport

end

end OAI
