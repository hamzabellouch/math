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

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma mfderiv_extChartAt_eq_tangentCoordChange {a y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y =
      tangentCoordChange 𝓘(ℝ,E) y a y := by
  have hy' : y ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hy
  rw [(hasMFDerivAt_extChartAt (I := 𝓘(ℝ,E)) hy').mfderiv,
    mfderiv_chartAt_eq_tangentCoordChange hy']

lemma coordinate_metric_chart_pairing {a y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (u v : TangentSpace 𝓘(ℝ,E) y) :
    riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y u)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v) = inner ℝ u v := by
  let c := extChartAt 𝓘(ℝ,E) a
  let e := trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a
  have hy' : y ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hy
  have hbase : y ∈ e.baseSet := hy'
  have hInv : ∀ w : TangentSpace 𝓘(ℝ,E) y,
      e.symmL ℝ y (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c y w) = w := by
    intro w
    have hh := e.symmL_continuousLinearMapAt (R := ℝ) hbase w
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy'] at hh
    exact hh
  erw [riemannianCoordinateMetric_apply,c.left_inv hy,hInv u,hInv v]

lemma hasMFDerivAt_of_coordinate_gradient {a : M} (z : TangentBundle 𝓘(ℝ,E) M)
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ,E) a).source) (f : M → ℝ) (τ : ℝ)
    (hD : HasFDerivAt (fun w : E => f ((extChartAt 𝓘(ℝ,E) a).symm w))
      (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a z.1)
        ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E))
          (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2))
      (extChartAt 𝓘(ℝ,E) a z.1)) :
    HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f z.1 (τ • innerSL ℝ z.2) := by
  let c := extChartAt 𝓘(ℝ,E) a
  have hz' : z.1 ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hz
  have hDc := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) hz').hasMFDerivAt
  have H := hD.hasMFDerivAt.comp z.1 hDc
  have heq : f =ᶠ[𝓝 z.1] (fun x : M => f (c.symm (c x))) := by
    filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with x hx
    rw [c.left_inv hx]
  have H' := H.congr_of_eventuallyEq heq
  apply H'.congr_mfderiv
  ext w
  change τ * riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a z.1)
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) z.1 w) = τ * inner ℝ z.2 w
  congr 1
  rw [tangent_chart_apply]
  rw [←mfderiv_extChartAt_eq_tangentCoordChange hz]
  exact coordinate_metric_chart_pairing hz z.2 w

end WeakMTWTransport

end

end OAI
