import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.GeodesicSpray

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_spray_energy_symm (a : TangentBundle 𝓘(ℝ,E) M) (q : E × E)
    (hq : q.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target) :
    riemannianCoordinateMetric a.1 q.1 q.2 q.2 =
      ‖((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm q).2‖ ^ 2 := by
  rw [riemannianCoordinateMetric_apply]
  have hbase : (extChartAt 𝓘(ℝ,E) a.1).symm q.1 ∈
      (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a.1).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) a.1).map_target hq
  rw [Trivialization.symmL_apply _ hbase]
  have he : (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a.1).symm
      ((extChartAt 𝓘(ℝ,E) a.1).symm q.1) q.2 =
      tangentCoordChange 𝓘(ℝ,E) a.1 ((extChartAt 𝓘(ℝ,E) a.1).symm q.1)
        ((extChartAt 𝓘(ℝ,E) a.1).symm q.1) q.2 :=
    (tangentBundleCore 𝓘(ℝ,E) M).localTriv_symm_apply (i := achart E a.1) hbase q.2
  rw [he]
  change inner ℝ ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm q).2
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm q).2 = _
  exact real_inner_self_eq_norm_sq _

lemma coordinate_spray_energy (a z : TangentBundle 𝓘(ℝ,E) M)
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source) :
    riemannianCoordinateMetric a.1
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).1
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).2
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).2 = ‖z.2‖ ^ 2 := by
  rw [coordinate_spray_energy_symm a _ ((extChartAt 𝓘(ℝ,E) a.1).map_source hz)]
  rw [(extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).left_inv
    ((tangent_chart_source_iff a z).mpr hz)]

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma spray_chart_hasDerivAt {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    HasDerivAt (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) ∘ γ)
      (coordinateGeodesicField (riemannianCoordinateMetric (γ t).1)
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ t))) t := by
  have hd := Filter.Eventually.self_of_nhds hγ.eventually_hasDerivAt
  rw [geodesicSpray_coordinates (γ t) (γ t)
    (mem_extChartAt_source (I := 𝓘(ℝ,E)) (γ t).1)] at hd
  exact hd

lemma spray_coordinate_energy_hasDerivAt {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    let q := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) ∘ γ
    HasDerivAt (fun s => riemannianCoordinateMetric (γ t).1 (q s).1 (q s).2 (q s).2) 0 t := by
  let q := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) ∘ γ
  have hd := spray_chart_hasDerivAt hγ
  have hqt : (q t).1 ∈ (extChartAt 𝓘(ℝ,E) (γ t).1).target :=
    (extChartAt 𝓘(ℝ,E) (γ t).1).map_source (mem_extChartAt_source (γ t).1)
  have hg : DifferentiableAt ℝ (riemannianCoordinateMetric (γ t).1) (q t).1 :=
    ((contDiffOn_riemannianCoordinateMetric (γ t).1).contDiffAt
      ((isOpen_extChartAt_target (γ t).1).mem_nhds hqt)).differentiableAt (by simp)
  have hpos : HasDerivAt (fun s => (q s).1) (q t).2 t :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
  have hvel : HasDerivAt (fun s => (q s).2)
      (-coordinateChristoffel (riemannianCoordinateMetric (γ t).1) (q t).1 (q t).2 (q t).2) t :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
  exact metric_speed_derivative (E := E) hg
    (riemannianCoordinateMetric_isInvertible hqt)
    (riemannianCoordinateMetric_symm _ _) hpos hvel

lemma hasDerivAt_spray_energy {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    HasDerivAt (fun s => ‖(γ s).2‖ ^ 2) 0 t := by
  apply (spray_coordinate_energy_hasDerivAt hγ).congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, (γ s).1 ∈ (extChartAt 𝓘(ℝ,E) (γ t).1).source := by
    have h := hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t))
    filter_upwards [h] with s hs
    exact (tangent_chart_source_iff (γ t) (γ s)).mp hs
  filter_upwards [hnear] with s hs
  exact (coordinate_spray_energy (γ t) (γ s) hs).symm

lemma spray_speed_constant {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {a b s t : ℝ}
    (hγ : IsMIntegralCurveOn γ (geodesicSpray (E := E)) (Ioo a b))
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) : ‖(γ s).2‖ = ‖(γ t).2‖ := by
  have hd (r : ℝ) (hr : r ∈ Ioo a b) := hasDerivAt_spray_energy
    (hγ.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hr))
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht
  nlinarith [norm_nonneg (γ s).2,norm_nonneg (γ t).2]

end WeakMTWTransport

end

end OAI
