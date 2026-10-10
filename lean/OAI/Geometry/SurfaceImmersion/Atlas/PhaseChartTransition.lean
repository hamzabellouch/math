import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts
import OAI.Geometry.SurfaceImmersion.Geometry.CurveSecondFields
import OAI.Geometry.SurfaceImmersion.Primitive.IntrinsicCrossingNaturality

namespace OAI

/-! The localized analytic maps have the same second forms as the actual
surface phase charts. This permits later curves to keep their own charts. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates RealModes SmallModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas

omit [CompactSpace M] in
lemma phaseRealChartMap_surface_germ (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (hw : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x] surfacePhaseMap (i : M) e F := by
  have ho := (A.outer_eventually_one_of_weight_ne_zero i hw).comp_tendsto
    ((surfacePhaseChart (i : M) e).continuousAt_symm hx)
  filter_upwards [(surfacePhaseChart (i : M) e).open_target.mem_nhds hx,ho] with y hy hoy
  have hyt : e.symm (baseEquiv.symm y) ∈ (chart (i : M)).target := hy.2
  change spaceCoordinates (A.vectorChartRead i F (e.symm (baseEquiv.symm y))) =
    spaceCoordinates (F ((chart (i : M)).symm (e.symm (baseEquiv.symm y))))
  change A.outer i ((chart (i : M)).symm (e.symm (baseEquiv.symm y))) = 1 at hoy
  simp only [vectorChartRead,localize,indicator_of_mem hyt,hoy,one_pow,one_smul]

omit [CompactSpace M] in
lemma phaseRealChartMap_transition_germ (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (i : M) e (j : M) f).source)
    (hwA : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (hwB : B.weight j ((surfacePhaseChart (i : M) e).symm x) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      B.phaseRealChartMap j f.symm F ∘ surfacePhaseTransition (i : M) e (j : M) f := by
  have hxA : x ∈ (surfacePhaseChart (i : M) e).target := hx.1
  have hxB : (surfacePhaseChart (i : M) e).symm x ∈ (surfacePhaseChart (j : M) f).source := hx.2
  let T := surfacePhaseTransition (i : M) e (j : M) f
  have hy : T x ∈ (surfacePhaseChart (j : M) f).target :=
    (surfacePhaseChart (j : M) f).map_source hxB
  have hwy : B.weight j ((surfacePhaseChart (j : M) f).symm (T x)) ≠ 0 := by
    change B.weight j ((surfacePhaseChart (j : M) f).symm
      ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (i : M) e).symm x))) ≠ 0
    rwa [(surfacePhaseChart (j : M) f).left_inv hxB]
  exact (A.phaseRealChartMap_surface_germ i e F hxA hwA).trans
    ((surfacePhaseMap_transition_germ (i : M) (j : M) e f F hx).trans
      (((B.phaseRealChartMap_surface_germ j f F hy hwy).comp_tendsto
        (T.continuousAt hx)).symm))

lemma phase_secondForm_transition (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (i : M) e (j : M) f).source)
    (hwA : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (hwB : B.weight j ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (v w : SmallModes.Base) :
    let T := surfacePhaseTransition (i : M) e (j : M) f
    realSecondForm (A.phaseRealChartMap i e.symm F) v w x =
      realSecondForm (B.phaseRealChartMap j f.symm F)
        (fderiv ℝ T x v) (fderiv ℝ T x w) (T x) := by
  let T := surfacePhaseTransition (i : M) e (j : M) f
  have hg := A.phaseRealChartMap_transition_germ B i j e f F hx hwA hwB
  have hxB : (surfacePhaseChart (i : M) e).symm x ∈ (surfacePhaseChart (j : M) f).source := hx.2
  have hy : T x ∈ (surfacePhaseChart (j : M) f).target :=
    (surfacePhaseChart (j : M) f).map_source hxB
  have hwy : B.chartWeight j (f.symm (baseEquiv.symm (T x))) ≠ 0 := by
    have hyw : B.weight j ((surfacePhaseChart (j : M) f).symm (T x)) ≠ 0 := by
      change B.weight j ((surfacePhaseChart (j : M) f).symm
        ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (i : M) e).symm x))) ≠ 0
      rwa [(surfacePhaseChart (j : M) f).left_inv hxB]
    have hyt : f.symm (baseEquiv.symm (T x)) ∈ (chart (j : M)).target := hy.2
    rw [chartWeight,indicator_of_mem hyt]
    simpa only [surfacePhaseChart_symm_apply] using hyw
  rw [(realSecondForm_eventuallyEq hg v w).eq_of_nhds]
  exact realSecondForm_comp_on T.open_source isOpen_univ
    (B.phaseRealChartMap_smooth j hfi hF.1).contDiffOn
    (surfacePhaseTransition_smooth (i : M) e hi (j : M) f hf) hx (mem_univ _) v w
    (B.phase_gram_ne_zero j f hf hfi hF hy.1 hwy)
    (surfacePhaseTransition_det_ne (i : M) e he hi (j : M) f hf hfi hx)

lemma phase_intrinsic_crossing_transition (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (i : M) e (j : M) f).source)
    (hwA : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (hwB : B.weight j ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (v w : SmallModes.Base) :
    let T := surfacePhaseTransition (i : M) e (j : M) f
    let H := A.phaseRealChartMap i e.symm F
    let G := B.phaseRealChartMap j f.symm F
    orderedCrossing H v w x
      (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) x) =
    orderedCrossing G (fderiv ℝ T x v) (fderiv ℝ T x w) (T x)
      (coordinateGaussianCurvature (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) (T x)) := by
  let T := surfacePhaseTransition (i : M) e (j : M) f
  have hxA : x ∈ (surfacePhaseChart (i : M) e).target := hx.1
  have htA : e.symm (baseEquiv.symm x) ∈ (chart (i : M)).target := hxA.2
  have ha : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0 := by
    rw [chartWeight,indicator_of_mem htA]
    exact hwA
  have hxB : (surfacePhaseChart (i : M) e).symm x ∈ (surfacePhaseChart (j : M) f).source := hx.2
  have hy : T x ∈ (surfacePhaseChart (j : M) f).target :=
    (surfacePhaseChart (j : M) f).map_source hxB
  have htB : f.symm (baseEquiv.symm (T x)) ∈ (chart (j : M)).target := hy.2
  have hb : B.chartWeight j (f.symm (baseEquiv.symm (T x))) ≠ 0 := by
    rw [chartWeight,indicator_of_mem htB]
    change B.weight j ((surfacePhaseChart (j : M) f).symm
      ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (i : M) e).symm x))) ≠ 0
    rwa [(surfacePhaseChart (j : M) f).left_inv hxB]
  dsimp only
  rw [orderedCrossing_intrinsic_eq (A.phaseRealChartMap_smooth i hi hF.1) x v w
      (A.phase_gram_ne_zero i e he hi hF hxA.1 ha),
    orderedCrossing_intrinsic_eq (B.phaseRealChartMap_smooth j hfi hF.1) (T x) _ _
      (B.phase_gram_ne_zero j f hf hfi hF hy.1 hb),
    A.phase_secondForm_transition B i j e f he hi hf hfi hF hx hwA hwB v w,
    A.phase_secondForm_transition B i j e f he hi hf hfi hF hx hwA hwB v v,
    A.phase_secondForm_transition B i j e f he hi hf hfi hF hx hwA hwB w w]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
