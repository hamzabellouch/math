import Mathlib
import OAI.Analysis.BiholderTransport.Model
import OAI.Analysis.BiholderTransport.Geodesics.SprayMinimizing
import OAI.Analysis.BiholderTransport.Geodesics.EndpointIdentity

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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma sprayFlow_isGeodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    IsGeodesicWithInitialData x v (fun t => (sprayFlow t ⟨x,v⟩).1) := by
  have hsm : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun t => sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const)
  refine ⟨(Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).comp hsm,?_,?_⟩
  · rw [spray_velocity_eq_mfderiv ((sprayFlow_curve ⟨x,v⟩).isMIntegralCurveAt 0)]
    exact sprayFlow_zero ⟨x,v⟩
  · exact sprayFlow_locally_minimizing ⟨x,v⟩

lemma exists_geodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ γ : ℝ → M, IsGeodesicWithInitialData x v γ :=
  ⟨_,sprayFlow_isGeodesicWithInitialData x v⟩

lemma riemannianExp_eq_chosen_geodesic (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    riemannianExp x v = Classical.choose (exists_geodesicWithInitialData x v) 1 := by
  rw [riemannianExp,dite_eq_left (exists_geodesicWithInitialData x v)]

end
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_flow_eq_spray (a : M) {r : ℝ} (hr : 0 < r)
    {Ψ W : ℝ × E → E}
    (hinit : ∀ v ∈ Metric.ball (0:E) r,
      Ψ (0,v) = extChartAt 𝓘(ℝ,E) a a ∧ W (0,v) = v)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball (0:E) r,
      Ψ (t,v) ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
      HasDerivAt (fun s => Ψ (s,v)) (W (t,v)) t ∧
      HasDerivAt (fun s => W (s,v))
        (-coordinateChristoffel (riemannianCoordinateMetric a) (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {v : E} (hv : v ∈ Metric.ball (0:E) r) {t : ℝ} (ht : t ∈ Ioo (-r) r) :
    Ψ (t,v) = extChartAt 𝓘(ℝ,E) a (sprayFlow t ⟨a,v⟩).1 := by
  let z : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
  have H := sprayFlow_eq_coordinate_curve z hr
    (fun s hs => (hode s hs v hv).1)
    (fun s hs => (hode s hs v hv).2.1.prodMk (hode s hs v hv).2.2)
    (show (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z).symm (Ψ (0,v), W (0,v)) = ⟨a,v⟩ by
      rw [(hinit v hv).1,(hinit v hv).2]
      exact tangent_chart_at_self_base_symm z v) ht
  have Hc := congrArg (fun p : TangentBundle 𝓘(ℝ,E) M => extChartAt 𝓘(ℝ,E) a p.1) H
  rw [tangent_chart_symm_base,(extChartAt 𝓘(ℝ,E) a).right_inv (hode t ht v hv).1] at Hc
  exact Hc.symm

lemma coordinate_endpoint_radial (a : M) {r : ℝ} (hr : 0 < r)
    {Ψ W : ℝ × E → E}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hinit : ∀ v ∈ Metric.ball (0:E) r,
      Ψ (0,v) = extChartAt 𝓘(ℝ,E) a a ∧ W (0,v) = v)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball (0:E) r,
      Ψ (t,v) ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
      HasDerivAt (fun s => Ψ (s,v)) (W (t,v)) t ∧
      HasDerivAt (fun s => W (s,v))
        (-coordinateChristoffel (riemannianCoordinateMetric a) (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {v : E} (hv : v ∈ Metric.ball (0:E) r) {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) :
    fderiv ℝ (fun w => Ψ (τ,w)) v v = τ • W (τ,v) := by
  have hn1 : ∀ᶠ s : ℝ in 𝓝 1, s • v ∈ Metric.ball (0:E) r :=
    ((continuousAt_id.smul continuousAt_const) : ContinuousAt (fun s : ℝ => s • v) 1)
      (by change Metric.ball (0:E) r ∈ 𝓝 ((1:ℝ) • v)
          simpa only [one_smul] using Metric.isOpen_ball.mem_nhds hv)
  have hn2 : ∀ᶠ s : ℝ in 𝓝 1, s*τ ∈ Ioo (-r) r :=
    ((continuousAt_id.mul continuousAt_const) :
      ContinuousAt (fun scalar : ℝ => scalar * τ) 1).preimage_mem_nhds
      (by change Ioo (-r) r ∈ 𝓝 ((1:ℝ)*τ)
          simpa only [one_mul] using isOpen_Ioo.mem_nhds hτ)
  have heq : (fun s : ℝ => Ψ (τ,s • v)) =ᶠ[𝓝 1] (fun s => Ψ (s*τ,v)) := by
    filter_upwards [hn1,hn2] with s hs ht
    rw [coordinate_flow_eq_spray a hr hinit hode hs hτ,
      coordinate_flow_eq_spray a hr hinit hode hv ht]
    rw [show (⟨a,s • v⟩ : TangentBundle 𝓘(ℝ,E) M) = tangentScale s ⟨a,v⟩ from rfl,
      sprayFlow_scale]
    rfl
  have hD : DifferentiableAt ℝ (fun w => Ψ (τ,w)) v :=
    ((hΨ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hτ,hv⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hleft : HasDerivAt (fun s : ℝ => Ψ (τ,s • v))
      (fderiv ℝ (fun w => Ψ (τ,w)) v v) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s • v) v 1 := by
      simpa only [one_smul] using (hasDerivAt_id' (1:ℝ)).smul_const v
    have hD' : HasFDerivAt (fun w => Ψ (τ,w))
        (fderiv ℝ (fun w => Ψ (τ,w)) v) ((1:ℝ) • v) := by
      simpa only [one_smul] using hD.hasFDerivAt
    exact hD'.comp_hasDerivAt 1 hs
  have hright : HasDerivAt (fun s : ℝ => Ψ (s*τ,v)) (τ • W (τ,v)) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s*τ) τ 1 := hasDerivAt_mul_const τ
    have hW : HasDerivAt (fun s => Ψ (s,v)) (W (τ,v)) ((1:ℝ)*τ) := by
      simpa only [one_mul] using (hode τ hτ v hv).2.1
    exact hW.scomp 1 hs
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

end WeakMTWTransport

end

end OAI
