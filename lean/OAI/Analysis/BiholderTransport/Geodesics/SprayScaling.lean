import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayProjection

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

def tangentScale (c : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) : TangentBundle 𝓘(ℝ,E) M :=
  ⟨z.1,c • z.2⟩

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma tangent_chart_scale (a z : TangentBundle 𝓘(ℝ,E) M) (c : ℝ) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (tangentScale c z) =
      ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).1,
        c • (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).2) := by
  simp only [tangent_chart_apply,tangentScale]
  congr 1
  exact (tangentCoordChange 𝓘(ℝ,E) z.1 a.1 z.1).map_smul c z.2

lemma isMIntegralCurve_spray_scaled {γ : ℝ → TangentBundle 𝓘(ℝ,E) M}
    (hγ : IsMIntegralCurve γ (geodesicSpray (E := E))) (c : ℝ) :
    IsMIntegralCurve (fun t => tangentScale c (γ (c*t))) (geodesicSpray (E := E)) := by
  intro t
  let a := γ (c*t)
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let P : ℝ → E × E := fun s => ((χ (γ (c*s))).1,c • (χ (γ (c*s))).2)
  have hd := coordinate_geodesic_scale (spray_chart_hasDerivAt (hγ.isMIntegralCurveAt (c*t)))
    (c := c)
  have hPt : (P t).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target := by
    change (χ a).1 ∈ _
    rw [tangent_chart_apply]
    exact mem_extChartAt_target a.1
  have hδ : (χ.symm ∘ P) =ᶠ[𝓝 t] (fun s => tangentScale c (γ (c*s))) := by
    have hc : ContinuousAt (fun s => γ (c*s)) t :=
      (hγ.isMIntegralCurveAt (c*t)).continuousAt.comp (continuousAt_const.mul continuousAt_id)
    have hn : ∀ᶠ s in 𝓝 t, γ (c*s) ∈ χ.source :=
      hc.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a)
    filter_upwards [hn] with s hs
    have hss : tangentScale c (γ (c*s)) ∈ χ.source :=
      (tangent_chart_source_iff a _).mpr ((tangent_chart_source_iff a _).mp hs)
    change χ.symm (P s) = _
    rw [show P s = χ (tangentScale c (γ (c*s))) from (tangent_chart_scale a _ c).symm]
    exact χ.left_inv hss
  have scaledDeriv :=
    (hasMFDerivAt_of_coordinate_spray a hPt hd).congr_of_eventuallyEq_abuse hδ.symm
  have scaledPoint : (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (P t) =
      tangentScale c (γ (c*t)) := hδ.self_of_nhds
  apply scaledDeriv.congr_mfderiv
  exact congrArg (fun point : TangentBundle 𝓘(ℝ,E) M =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (show E × E from geodesicSpray point)) scaledPoint

variable [T2Space M] [CompactSpace M]

lemma sprayFlow_scale (z : TangentBundle 𝓘(ℝ,E) M) (c t : ℝ) :
    sprayFlow t (tangentScale c z) = tangentScale c (sprayFlow (c*t) z) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (contMDiff_geodesicSpray.of_le (by simp)) (sprayFlow_curve (tangentScale c z))
    (isMIntegralCurve_spray_scaled (sprayFlow_curve z) c)
    (by simp only [sprayFlow_zero,mul_zero])
  exact congrFun he t

end WeakMTWTransport

end

end OAI
