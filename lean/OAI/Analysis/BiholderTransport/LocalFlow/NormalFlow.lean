import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.JointNormalChart
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_metric_normal_flow (a : M) :
    ∃ δ r τ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < τ ∧ τ < r ∧
    ∃ Ψ W : ℝ × E → E, ∃ e : OpenPartialHomeomorph E E,
      ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r) ∧
      ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball (0:E) r, Ψ (0,v) = extChartAt 𝓘(ℝ,E) a a ∧ W (0,v) = v) ∧
      (∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball (0:E) r,
        Ψ (t,v) ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
        HasDerivAt (fun s => Ψ (s,v)) (W (t,v)) t ∧
        HasDerivAt (fun s => W (s,v))
          (-coordinateChristoffel (riemannianCoordinateMetric a) (Ψ (t,v)) (W (t,v)) (W (t,v))) t) ∧
      (e : E → E) = (fun v => Ψ (τ,v)) ∧
      0 ∈ e.source ∧ e 0 = extChartAt 𝓘(ℝ,E) a a ∧ e.source ⊆ Metric.ball (0:E) r ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (Metric.ball a δ ⊆ (extChartAt 𝓘(ℝ,E) a).source ∩
        (extChartAt 𝓘(ℝ,E) a) ⁻¹' e.target) ∧
      (∀ y ∈ Metric.ball a δ, dist a y = τ *
        Real.sqrt (riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a a)
          (e.symm (extChartAt 𝓘(ℝ,E) a y)) (e.symm (extChartAt 𝓘(ℝ,E) a y)))) ∧
      fderiv ℝ e 0 = τ • ContinuousLinearMap.id ℝ E := by
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,hode,he,hesub,hed,hei,hsrc,hdiag,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  let c := extChartAt 𝓘(ℝ,E) a
  let x := c a
  let Ψ : ℝ × E → E := fun z => (Φ (z.1,(x,z.2))).1
  let W : ℝ × E → E := fun z => (Φ (z.1,(x,z.2))).2
  have hball : ∀ v ∈ Metric.ball (0:E) r, (x,v) ∈ Metric.ball (x,0) r := by
    intro v hv
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hr hv
  have hΦc := hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    (show MapsTo (fun z : ℝ × E => (z.1,(x,z.2)))
      (Ioo (-r) r ×ˢ Metric.ball 0 r) (Ioo (-r) r ×ˢ Metric.ball (x,0) r) from
      fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
  have hp : ∀ z : E × E, (e z).1 = z.1 := by intro z; rw [he]
  let f := fiberwiseHomeomorph e hp x
  have hf : (f : E → E) = fun v => Ψ (τ,v) := by funext v; change (e (x,v)).2 = _; rw [he]
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have haz : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
  have hzero := coordinate_geodesic_zero_velocity
    (fun t ht' => ((contDiffOn_riemannianCoordinateMetric a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds
        (hode t ht' (x,0) (Metric.mem_ball_self hr)).1)).differentiableAt (by simp))
    (fun t ht' => riemannianCoordinateMetric_isInvertible
      (hode t ht' (x,0) (Metric.mem_ball_self hr)).1)
    (fun t ht' _ hv => riemannianCoordinateMetric_positive
      (hode t ht' (x,0) (Metric.mem_ball_self hr)).1 hv)
    (fun t _ u v => riemannianCoordinateMetric_symm a _ u v)
    (fun t ht' => ⟨((hode t ht' (x,0) (Metric.mem_ball_self hr)).2).fst,
      ((hode t ht' (x,0) (Metric.mem_ball_self hr)).2).snd⟩) h0
    (show (Φ (0,(x,0))).2 = 0 from congrArg Prod.snd (hΦ0 (x,0) (Metric.mem_ball_self hr))) ht
  have hf0 : f 0 = x := by
    rw [hf]
    exact hzero.1.trans (congrArg Prod.fst (hΦ0 (x,0) (Metric.mem_ball_self hr)))
  refine ⟨δ,r,τ,hδ,hr,hτ,hτr,Ψ,W,f,hΦc.fst,hΦc.snd,?_,?_,hf,hdiag a haz,hf0,?_,
    fiberwiseHomeomorph_contDiffOn hp x hed,fiberwiseHomeomorph_symm_contDiffOn hp x hei,?_,?_,?_⟩
  · intro v hv
    exact ⟨congrArg Prod.fst (hΦ0 (x,v) (hball v hv)),congrArg Prod.snd (hΦ0 (x,v) (hball v hv))⟩
  · intro t ht' v hv
    exact ⟨(hode t ht' (x,v) (hball v hv)).1,
      ((hode t ht' (x,v) (hball v hv)).2).fst,((hode t ht' (x,v) (hball v hv)).2).snd⟩
  · intro v hv
    exact (max_lt_iff.mp (show max (dist x x) (dist v 0) < r from hesub hv)).2
  · intro y hy
    exact ⟨hsrc hy,htarget a haz y hy⟩
  · intro y hy
    apply hdist a haz y hy (f.symm (c y))
    · exact f.map_target (htarget a haz y hy)
    · change Ψ (τ,f.symm (c y)) = c y
      exact (congrFun hf _).symm.trans (f.right_inv (htarget a haz y hy))
  · rw [hf]
    exact coordinate_flow_endpoint_derivative_zero a hr hΦ hΦ0 hode ht

end WeakMTWTransport

end

end OAI
