import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.TangentLift
import OAI.Analysis.BiholderTransport.Coordinates.ChartTransition

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

namespace WeakMTWTransport
open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma tangent_chart_source_iff (a z : TangentBundle 𝓘(ℝ,E) M) :
    z ∈ (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).source ↔
      z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source := by
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_source,PartialEquiv.prod_source,PartialEquiv.refl_source,
    Trivialization.source_eq,mem_inter_iff,mem_preimage,
    mem_prod,mem_univ,and_true,TangentBundle.trivializationAt_baseSet]
  simp only [extChartAt_source]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h,?_⟩
    change (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a.1 z).1 ∈ (chartAt E a.1).source
    rwa [TangentBundle.trivializationAt_apply]

lemma tangent_chart_transition_eventually (a b : TangentBundle 𝓘(ℝ,E) M)
    {z : E × E} (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hb : (extChartAt 𝓘(ℝ,E) a.1).symm z.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source) :
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) b ∘
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm) =ᶠ[𝓝 z]
      coordinateTangentLift (extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm) := by
  have h1 : ∀ᶠ y in 𝓝 z, y.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a.1).mem_nhds ha)
  have h2 : ∀ᶠ y in 𝓝 z,
      (extChartAt 𝓘(ℝ,E) a.1).symm y.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source :=
    ((continuousAt_extChartAt_symm'' ha).comp continuousAt_fst).preimage_mem_nhds
      ((isOpen_extChartAt_source b.1).mem_nhds hb)
  filter_upwards [h1,h2] with y hy1 hy2
  exact tangent_chart_transition_apply a b y hy1 hy2

lemma tangent_tangentCoordChange_apply (a b z : TangentBundle 𝓘(ℝ,E) M)
    (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source)
    (hb : z.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source) (w : E × E) :
    tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a b z w =
      fderiv ℝ (coordinateTangentLift
        (extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm))
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z) w := by
  have heq := tangent_chart_transition_eventually a b
    (z := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z)
    ((extChartAt 𝓘(ℝ,E) a.1).map_source ha)
    (by simpa only [tangent_chart_apply,(extChartAt 𝓘(ℝ,E) a.1).left_inv ha] using hb)
  simp only [tangentCoordChange_def,ModelWithCorners.range_eq_univ,fderivWithin_univ]
  exact congrArg (fun L : (E × E) →L[ℝ] (E × E) => L w) heq.fderiv_eq

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma riemannianCoordinateMetric_isInvertible [FiniteDimensional ℝ E] {a : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) a).target) :
    (riemannianCoordinateMetric a z).IsInvertible :=
  metricDual_isInvertible _ (fun _ hv => riemannianCoordinateMetric_positive hz hv)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma riemannianMetric_transition_eventually {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,E) a x), ∀ u v,
      riemannianCoordinateMetric a y u v =
        riemannianCoordinateMetric b
          ((extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm) y)
          (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm) y u)
          (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm) y v) := by
  have ht := (extChartAt 𝓘(ℝ,E) a).map_source ha
  have h1 := (isOpen_extChartAt_target a).mem_nhds ht
  have h2 : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,E) a x),
      (extChartAt 𝓘(ℝ,E) a).symm y ∈ (extChartAt 𝓘(ℝ,E) b).source :=
    (continuousAt_extChartAt_symm'' ht).preimage_mem_nhds
      (by simpa only [(extChartAt 𝓘(ℝ,E) a).left_inv ha] using
        (isOpen_extChartAt_source b).mem_nhds hb)
  filter_upwards [h1,h2] with y hy1 hy2
  have hy0 := (extChartAt 𝓘(ℝ,E) a).map_target hy1
  intro u v
  have h := chart_metric_transition hy0 hy2
    (g := riemannianCoordinateMetric a) (h := riemannianCoordinateMetric b)
    (fun u v => by rw [riemannianCoordinateMetric_apply,(extChartAt 𝓘(ℝ,E) a).left_inv hy0])
    (fun u v => by rw [riemannianCoordinateMetric_apply,(extChartAt 𝓘(ℝ,E) b).left_inv hy2]) u v
  simpa only [(extChartAt 𝓘(ℝ,E) a).right_inv hy1,Function.comp_apply] using h

def geodesicSpray (z : TangentBundle 𝓘(ℝ,E) M) :
    TangentSpace (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z :=
  coordinateGeodesicField (riemannianCoordinateMetric z.1)
    (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2)

lemma geodesicSpray_coordinates [FiniteDimensional ℝ E] (a z : TangentBundle 𝓘(ℝ,E) M)
    (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source) :
    tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z a z (geodesicSpray z) =
      coordinateGeodesicField (riemannianCoordinateMetric a.1)
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z) := by
  have hz := mem_extChartAt_source (I := 𝓘(ℝ,E)) z.1
  have htz := (extChartAt 𝓘(ℝ,E) z.1).map_source hz
  have hta := (extChartAt 𝓘(ℝ,E) a.1).map_source ha
  change tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z a z
    (coordinateGeodesicField (riemannianCoordinateMetric z.1)
      (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2)) = _
  rw [tangent_tangentCoordChange_apply z a z hz ha]
  have hφ := contDiffAt_chart_transition hz ha
  have he := coordinateTangentLift_push_geodesicField (E := E)
    ((contDiffOn_riemannianCoordinateMetric z.1).contDiffAt
      ((isOpen_extChartAt_target z.1).mem_nhds htz) |>.differentiableAt (by simp))
    (g := riemannianCoordinateMetric z.1) (h := riemannianCoordinateMetric a.1)
    (φ := extChartAt 𝓘(ℝ,E) a.1 ∘ (extChartAt 𝓘(ℝ,E) z.1).symm)
    (v := z.2)
    (by simpa only [Function.comp_apply,(extChartAt 𝓘(ℝ,E) z.1).left_inv hz] using
      ((contDiffOn_riemannianCoordinateMetric a.1).contDiffAt
        ((isOpen_extChartAt_target a.1).mem_nhds hta) |>.differentiableAt (by simp)))
    hφ (chart_transition_derivative_surjective hz ha)
    (riemannianMetric_transition_eventually hz ha)
    (riemannianCoordinateMetric_isInvertible htz)
    (by simpa only [Function.comp_apply,(extChartAt 𝓘(ℝ,E) z.1).left_inv hz] using
      riemannianCoordinateMetric_isInvertible hta)
    (riemannianCoordinateMetric_symm a.1 _)
  have hcoord : extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z z =
      (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2) := by
    rw [tangent_chart_apply]
    exact congrArg (fun v : E => (extChartAt 𝓘(ℝ,E) z.1 z.1,v))
      (tangentCoordChange_self (I := 𝓘(ℝ,E)) (v := z.2) hz)
  have hlift : coordinateTangentLift
      (extChartAt 𝓘(ℝ,E) a.1 ∘ (extChartAt 𝓘(ℝ,E) z.1).symm)
      (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2) =
      extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z := by
    rw [tangent_chart_apply]
    simp only [coordinateTangentLift,Function.comp_apply,
      (extChartAt 𝓘(ℝ,E) z.1).left_inv hz,(hasFDerivAt_chart_transition hz ha).fderiv]
  rw [hcoord]
  rw [hlift] at he
  convert! he using 1

lemma contMDiff_geodesicSpray [FiniteDimensional ℝ E] :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E))
      ((𝓘(ℝ,E).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,E × E)) ∞
      (fun z : TangentBundle 𝓘(ℝ,E) M =>
        (⟨z,geodesicSpray z⟩ : TangentBundle (𝓘(ℝ,E).prod 𝓘(ℝ,E)) _)) := by
  intro a
  apply (Bundle.contMDiffAt_section a).mpr
  have ha := mem_extChartAt_source (I := 𝓘(ℝ,E)) a.1
  have hat := (extChartAt 𝓘(ℝ,E) a.1).map_source ha
  have hg := (contDiffOn_riemannianCoordinateMetric a.1).contDiffAt
    ((isOpen_extChartAt_target a.1).mem_nhds hat)
  have hf := contDiffAt_coordinateGeodesicField (E := E) (v := a.2) hg
    (riemannianCoordinateMetric_isInvertible hat)
  have hself : extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a a =
      (extChartAt 𝓘(ℝ,E) a.1 a.1,a.2) := by
    rw [tangent_chart_apply]
    exact congrArg (fun v : E => (extChartAt 𝓘(ℝ,E) a.1 a.1,v))
      (tangentCoordChange_self (I := 𝓘(ℝ,E)) (v := a.2) ha)
  have hf' : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E × E) ∞
      (coordinateGeodesicField (riemannianCoordinateMetric a.1))
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a a) := by
    rw [hself]
    exact hf.contMDiffAt
  have hc := (contMDiffOn_extChartAt (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E))
    (n := ∞) (x := a)).contMDiffAt
    (by simpa only [extChartAt_source] using
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).mem_nhds
        (mem_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a)))
  apply (hf'.comp a hc).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).mem_nhds
        (mem_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a)] with z hz
  change tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z a z (geodesicSpray z) = _
  exact geodesicSpray_coordinates a z ((tangent_chart_source_iff a z).mp hz)

end WeakMTWTransport

end

end OAI
