import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateVariation
import OAI.Analysis.BiholderTransport.Geodesics.CompleteSpray
import OAI.Analysis.BiholderTransport.LocalFlow.SmoothIntegralCurve

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

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma hasMFDerivAt_spray_projection {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).1) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) := by
  have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t
    (spray_chart_hasDerivAt hγ)
  have ht := mem_extChartAt_source (I := 𝓘(ℝ,E)) (γ t).1
  have hself : (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ t)).2 =
      (γ t).2 := by
    rw [tangent_chart_apply]
    exact tangentCoordChange_self ht
  change HasDerivAt (fun s => (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ s)).1)
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ t)).2 t at hd
  rw [hself] at hd
  have hd' : HasDerivAt (extChartAt 𝓘(ℝ,E) (γ t).1 ∘ (fun s => (γ s).1))
      (γ t).2 t := by
    simpa only [Function.comp_def,tangent_chart_apply] using hd
  refine ⟨(FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt.comp
    hγ.continuousAt,?_⟩
  rw [writtenInExtChartAt,extChartAt_model_space_eq_id,ModelWithCorners.range_eq_univ]
  change HasFDerivWithinAt (extChartAt 𝓘(ℝ,E) (γ t).1 ∘ (fun s => (γ s).1))
    ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) univ t
  rw [hasFDerivWithinAt_univ]
  convert! hd'.hasFDerivAt using 1

lemma spray_velocity_eq_mfderiv {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).1) t (1 : ℝ) = (γ t).2 := by
  have h := congrArg (fun f : TangentSpace 𝓘(ℝ,ℝ) t →L[ℝ]
    TangentSpace 𝓘(ℝ,E) (γ t).1 => f (1 : ℝ)) (hasMFDerivAt_spray_projection hγ).mfderiv
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).1) t (1 : ℝ) =
    (1 : ℝ) • (γ t).2 at h
  simpa only [one_smul] using h

variable [T2Space M] [CompactSpace M]

def sprayFlow (t : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) : TangentBundle 𝓘(ℝ,E) M :=
  completeFlow exists_complete_spray_curve t z

lemma sprayFlow_zero (z : TangentBundle 𝓘(ℝ,E) M) : sprayFlow 0 z = z :=
  completeFlow_zero exists_complete_spray_curve z

lemma sprayFlow_curve (z : TangentBundle 𝓘(ℝ,E) M) :
    IsMIntegralCurve (fun t => sprayFlow t z) (geodesicSpray (E := E)) :=
  completeFlow_curve exists_complete_spray_curve z

lemma sprayFlow_add (s t : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) :
    sprayFlow (s+t) z = sprayFlow s (sprayFlow t z) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  exact completeFlow_add exists_complete_spray_curve contMDiff_geodesicSpray s t z

lemma contMDiff_sprayFlow :
    ContMDiff (𝓘(ℝ,ℝ).prod (𝓘(ℝ,E).prod 𝓘(ℝ,E))) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun z : ℝ × TangentBundle 𝓘(ℝ,E) M => sprayFlow z.1 z.2) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  exact contMDiff_completeFlow exists_complete_spray_curve contMDiff_geodesicSpray

lemma sprayFlow_speed (t : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) :
    ‖(sprayFlow t z).2‖ = ‖z.2‖ := by
  have he := spray_speed_constant ((sprayFlow_curve z).isMIntegralCurveOn (Ioo (min t 0-1) (max t 0+1)))
    (show t ∈ Ioo (min t 0-1) (max t 0+1) from
      ⟨by linarith [min_le_left t 0],by linarith [le_max_left t 0]⟩)
    (show (0:ℝ) ∈ Ioo (min t 0-1) (max t 0+1) from
      ⟨by linarith [min_le_right t 0],by linarith [le_max_right t 0]⟩)
  exact he.trans (congrArg (fun w : TangentBundle 𝓘(ℝ,E) M => ‖w.2‖) (sprayFlow_zero z))

end
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma tangent_chart_target_iff (a : TangentBundle 𝓘(ℝ,E) M) (q : E × E) :
    q ∈ (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).target ↔
      q.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target := by
  rw [FiberBundle.extChartAt_target]
  constructor
  · exact fun h => h.1.1
  · intro h
    refine ⟨⟨h,?_⟩,mem_univ _⟩
    simpa only [TangentBundle.trivializationAt_baseSet,← extChartAt_source 𝓘(ℝ,E),mem_preimage] using
      (extChartAt 𝓘(ℝ,E) a.1).map_target h

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma hasMFDerivAt_of_coordinate_spray (a : TangentBundle 𝓘(ℝ,E) M)
    {q : ℝ → E × E} {t : ℝ} (hq : (q t).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hd : HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q t)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E))
      ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm ∘ q) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicSpray ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (q t)))) := by
  have hqt := (tangent_chart_target_iff a (q t)).mpr hq
  apply hasMFDerivAt_of_chart_ode a hqt
  rw [geodesicSpray_coordinates a _ ((tangent_chart_source_iff a _).mp
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).map_target hqt)),
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).right_inv hqt]
  exact hd

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma coordinate_geodesic_scale {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {q : ℝ → E × E} {t c : ℝ}
    (hq : HasDerivAt q (coordinateGeodesicField g (q (c*t))) (c*t)) :
    HasDerivAt (fun s => ((q (c*s)).1,c • (q (c*s)).2))
      (coordinateGeodesicField g ((q (c*t)).1,c • (q (c*t)).2)) t := by
  have hq₁ : HasDerivAt (fun s => (q s).1) (q (c*t)).2 (c*t) :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt (c*t) hq
  have hq₂ : HasDerivAt (fun s => (q s).2)
      (-coordinateChristoffel g (q (c*t)).1 (q (c*t)).2 (q (c*t)).2) (c*t) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt (c*t) hq
  have h₁ := hq₁.scomp t ((hasDerivAt_id t).const_mul c)
  have h₂ := (hq₂.scomp t ((hasDerivAt_id t).const_mul c)).const_smul c
  have h := h₁.prodMk h₂
  convert! h using 1
  simp only [coordinateGeodesicField,coordinateChristoffel_smul_left,
    coordinateChristoffel_smul_right,mul_one,smul_neg]

variable [T2Space M] [CompactSpace M]

lemma sprayFlow_eq_coordinate_curve (a : TangentBundle 𝓘(ℝ,E) M)
    {q : ℝ → E × E} {r : ℝ} (hr : 0 < r)
    (himg : ∀ t ∈ Ioo (-r) r, (q t).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hode : ∀ t ∈ Ioo (-r) r,
      HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q t)) t)
    {z : TangentBundle 𝓘(ℝ,E) M}
    (hq0 : (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (q 0) = z)
    {t : ℝ} (ht : t ∈ Ioo (-r) r) :
    sprayFlow t z = (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (q t) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨neg_lt_zero.mpr hr,hr⟩ (contMDiff_geodesicSpray.of_le (by simp))
    ((sprayFlow_curve z).isMIntegralCurveOn _) _ _ ht
  · intro s hs
    exact (hasMFDerivAt_of_coordinate_spray a (himg s hs) (hode s hs)).hasMFDerivWithinAt
  · exact (sprayFlow_zero z).trans hq0.symm

end WeakMTWTransport

end

end OAI
