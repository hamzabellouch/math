import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricReadGerms
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasBoundaryProfile
import OAI.Geometry.SurfaceImmersion.Atlas.ImmersedAtlasNormal
import OAI.Geometry.SurfaceImmersion.Geometry.MetricConnectionNaturality
import OAI.Geometry.SurfaceImmersion.Atlas.RealPhaseChart

namespace OAI

/-! Strict convexity of the prescribed surface metric gives the exact
positive transverse Hessian used by the actual phase-coordinate loop. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry SurfaceJetCoordinates

lemma coordinateMetricHessian_congr_germ {h k : Base → PhaseMean.Tensor} {p : Base}
    (hh : h =ᶠ[𝓝 p] k) (phi : Base → ℝ) (v w : Base) :
    coordinateMetricHessian h phi p v w = coordinateMetricHessian k phi p v w := by
  simp only [coordinateMetricHessian,hh.eq_of_nhds,hh.fderiv_eq]

namespace FiniteOrderSmoothing.SmoothingAtlas
open JetPolynomial
local instance phaseConvexFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseConvexFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance phaseConvexDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseConvexDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance phaseConvexSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseConvexSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable (A : SmoothingAtlas M)

lemma realChartMap_metric_germ (i : A.centers) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M} (hp : A.weight i p ≠ 0)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    inducedCoordinateMetric (A.realChartMap i F) =ᶠ[𝓝 (coordinateChart (i : M) p)]
      coordinateMetric g (i : M) := by
  have hs := A.weight_support i (subset_tsupport _ hp)
  have hw : A.chartWeight i (baseEquiv.symm (coordinateChart (i : M) p)) ≠ 0 := by
    rw [show coordinateChart (i : M) p = baseEquiv (chart (i : M) p) from rfl,
      baseEquiv.symm_apply_apply]
    rw [chartWeight,indicator_of_mem ((chart (i : M)).map_source hs),(chart (i : M)).left_inv hs]
    exact hp
  have hmetric : g.inner = inducedTensor F := by
    funext q; ext v w; exact (hF.2 q v w).symm
  have hc : Continuous (fun y : SmallModes.Base => A.chartWeight i (baseEquiv.symm y)) :=
    (A.chartWeight_smooth i).continuous.comp baseEquiv.symm.continuous
  have hr : inducedCoordinateMetric (A.realChartMap i F) =ᶠ[𝓝 (coordinateChart (i : M) p)]
      A.tensorPlaneRead i g.inner := by
    filter_upwards [(isOpen_ne.preimage hc).mem_nhds hw] with y hy
    have hh := A.metric_read_on_weight i hF.1 hy
    rw [← hmetric] at hh
    change realMetricTensor (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)
      (planeCoordinateIsometry (baseEquiv.symm y)) = _ at hh
    have hb : planeCoordinateIsometry (baseEquiv.symm y) = y := by
      change baseEquiv (baseEquiv.symm y) = y
      exact baseEquiv.apply_symm_apply y
    rw [hb] at hh
    exact hh
  exact hr.trans (A.tensorPlaneRead_metric_germ g i hs ho)

theorem phase_hessian_positive_of_metric (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {phi : SmallModes.Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (realPhaseChart e x).1 = phi x)
    {p : M} (hp : p ∈ (surfacePhaseChart (i : M) e).source) (hw : A.weight i p ≠ 0)
    (hpositive : ∀ v : SmallModes.Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (i : M)) phi (coordinateChart (i : M) p) v v) :
    0 < coordinateMetricHessian (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst (baseEquiv (e (chart (i : M) p))) dy dy := by
  let er := realPhaseChart e
  let x := baseEquiv (e (chart (i : M) p))
  have hx : x ∈ er.target := by
    change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) ∈ e.target
    rw [baseEquiv.symm_apply_apply]
    exact e.map_source hp.2
  have hback : er.symm x = coordinateChart (i : M) p := by
    change baseEquiv (e.symm (baseEquiv.symm (baseEquiv (e (chart (i : M) p))))) = _
    rw [baseEquiv.symm_apply_apply]
    have hps : chart (i : M) p ∈ e.source := hp.2
    exact (congrArg baseEquiv (e.left_inv hps)).trans (show baseEquiv (chart (i : M) p) = coordinateChart (i : M) p from rfl)
  have her := realPhaseChart_smooth e he
  have hir := realPhaseChart_symm_smooth e hi
  have hcomp : phi ∘ er.symm =ᶠ[𝓝 x] Prod.fst := by
    filter_upwards [er.open_target.mem_nhds hx] with y hy
    change phi (er.symm y) = y.1
    rw [← hphase,er.right_inv hy]
  have hdet : coordDet (fderiv ℝ er.symm x) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse er.open_target er.open_source hir.contDiffOn
      her.contDiffOn er.symm.mapsTo (fun y hy => er.right_inv hy) hx
  have hg := A.planeRead_gram_of_immersion hF.1 (IsSmoothIsometricImmersion.mfderiv_injective hF)
    houter i (subset_tsupport _ hw)
  have hI : Function.Injective (fderiv ℝ (A.realChartMap i F) (er.symm x)) := by
    rw [hback]
    exact injective_of_gramDet_ne_zero _ hg
  have hH := phase_chart_hessian_dy (A.realChartMap_smooth i hF.1) hphi hir x hcomp hI hdet
  have hmap : A.phaseRealChartMap i e.symm F = A.realChartMap i F ∘ er.symm := by
    funext y
    simp only [phaseRealChartMap,realChartMap,Function.comp_apply,er,realPhaseChart_symm_apply]
    have hb : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) = baseEquiv := rfl
    have hbs : (planeCoordinateIsometry.symm : SmallModes.Base → JetPolynomial.Base) = baseEquiv.symm := rfl
    rw [hb,hbs,baseEquiv.symm_apply_apply]
  rw [hmap,hH,hback,
    coordinateMetricHessian_congr_germ (A.realChartMap_metric_germ i hF hw (houter i p (subset_tsupport _ hw)))]
  apply hpositive
  have hI' := inverse_chart_derivative_injective er her hir hx
  intro hz
  have hh : (dy : SmallModes.Base) = 0 := hI' (hz.trans (map_zero _).symm)
  exact (show (dy : SmallModes.Base) ≠ 0 by simp [dy]) hh

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
