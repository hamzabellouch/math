import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayScaling

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
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma tangent_chart_at_self_base (a : TangentBundle 𝓘(ℝ,E) M) (v : E) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a ⟨a.1,v⟩ = (extChartAt 𝓘(ℝ,E) a.1 a.1,v) := by
  rw [tangent_chart_apply,tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ,E)) a.1)]

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma tangent_chart_at_self_base_symm (a : TangentBundle 𝓘(ℝ,E) M) (v : E) :
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (extChartAt 𝓘(ℝ,E) a.1 a.1,v) = ⟨a.1,v⟩ := by
  rw [←tangent_chart_at_self_base a v]
  exact (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).left_inv
    ((tangent_chart_source_iff a _).mpr (mem_extChartAt_source (I := 𝓘(ℝ,E)) a.1))

lemma hasDerivAt_spray_coordinate_zero (a : M) (v : TangentSpace 𝓘(ℝ,E) a) :
    HasDerivAt (fun t => extChartAt 𝓘(ℝ,E) a (sprayFlow t ⟨a,v⟩).1) v 0 := by
  have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0
    (spray_chart_hasDerivAt ((sprayFlow_curve (⟨a,v⟩ : TangentBundle 𝓘(ℝ,E) M)).isMIntegralCurveAt 0))
  simp only [sprayFlow_zero,tangent_chart_apply,coordinateGeodesicField,
    Function.comp_def,ContinuousLinearMap.coe_fst'] at hd
  have he : tangentCoordChange 𝓘(ℝ,E) a a a v = v :=
    tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ,E)) a)
  rw [he] at hd
  exact hd

lemma coordinate_flow_endpoint_derivative_zero (a : M) {r τ : ℝ} (hr : 0 < r)
    {Φ : ℝ × (E × E) → E × E}
    (hΦ : ContDiffOn ℝ ∞ Φ
      (Ioo (-r) r ×ˢ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r))
    (hΦ0 : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r, Φ (0,z) = z)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r,
      (Φ (t,z)).1 ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
      HasDerivAt (fun s => Φ (s,z)) (coordinateGeodesicField (riemannianCoordinateMetric a) (Φ (t,z))) t)
    (hτ : τ ∈ Ioo (-r) r) :
    fderiv ℝ (fun v : E => (Φ (τ,extChartAt 𝓘(ℝ,E) a a,v)).1) 0 =
      τ • ContinuousLinearMap.id ℝ E := by
  let x := extChartAt 𝓘(ℝ,E) a a
  let ψ : E → E := fun v => (Φ (τ,x,v)).1
  have hψ : DifferentiableAt ℝ ψ 0 :=
    (((hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨hτ,Metric.mem_ball_self hr⟩)).comp 0
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).fst).differentiableAt (by simp)
  have heq : ∀ v ∈ Metric.ball (0:E) r,
      ψ v = extChartAt 𝓘(ℝ,E) a (sprayFlow τ ⟨a,v⟩).1 := by
    intro v hv
    have hz : (x,v) ∈ Metric.ball (x,0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hr hv
    let z : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
    have H := sprayFlow_eq_coordinate_curve z hr
      (fun t ht => (hode t ht (x,v) hz).1)
      (fun t ht => (hode t ht (x,v) hz).2)
      (show (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z).symm (Φ (0,x,v)) = ⟨a,v⟩ by
        rw [hΦ0 (x,v) hz]; exact tangent_chart_at_self_base_symm z v) hτ
    have Hc := congrArg (fun p : TangentBundle 𝓘(ℝ,E) M => extChartAt 𝓘(ℝ,E) a p.1) H
    rw [tangent_chart_symm_base,(extChartAt 𝓘(ℝ,E) a).right_inv (hode τ hτ (x,v) hz).1] at Hc
    exact Hc.symm
  ext w
  have hn : ∀ᶠ s : ℝ in 𝓝 0, s • w ∈ Metric.ball (0:E) r :=
    ((continuousAt_id.smul continuousAt_const) :
      ContinuousAt (fun s : ℝ => s • w) 0).preimage_mem_nhds
      (by
        change Metric.ball (0:E) r ∈ 𝓝 ((0:ℝ) • w)
        simpa only [zero_smul] using Metric.ball_mem_nhds (0:E) hr)
  have he : (fun s : ℝ => ψ (s • w)) =ᶠ[𝓝 0]
      (fun s => extChartAt 𝓘(ℝ,E) a (sprayFlow (s*τ) ⟨a,w⟩).1) := by
    filter_upwards [hn] with s hs
    rw [heq (s • w) hs,show (⟨a,s • w⟩ : TangentBundle 𝓘(ℝ,E) M) = tangentScale s ⟨a,w⟩ from rfl,
      sprayFlow_scale]
    rfl
  have hL := (show HasFDerivAt ψ (fderiv ℝ ψ 0) ((0:ℝ) • w) by
    simpa only [zero_smul] using hψ.hasFDerivAt).comp_hasDerivAt 0
    (show HasDerivAt (fun s : ℝ => s • w) w 0 by
      simpa only [one_smul,id_eq] using (hasDerivAt_id (0:ℝ)).smul_const w)
  have hR := (show HasDerivAt (fun t => extChartAt 𝓘(ℝ,E) a
      (sprayFlow t ⟨a,w⟩).1) w ((id (0:ℝ))*τ) by
    simpa only [id_eq,zero_mul] using hasDerivAt_spray_coordinate_zero a w).scomp 0
      ((hasDerivAt_id (0:ℝ)).mul_const τ)
  have H := (hL.congr_of_eventuallyEq he.symm).unique
    (show HasDerivAt (fun s => extChartAt 𝓘(ℝ,E) a (sprayFlow (s*τ) ⟨a,w⟩).1) (τ • w) 0 by
      simpa only [zero_mul,one_mul,id_eq,Function.comp_def,smul_eq_mul] using hR)
  exact H

end WeakMTWTransport

end

end OAI
