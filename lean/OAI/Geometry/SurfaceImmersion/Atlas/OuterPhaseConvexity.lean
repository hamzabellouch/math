import OAI.Geometry.SurfaceImmersion.Atlas.OuterPhaseGeometry

namespace OAI

/-! The transverse phase Hessian stays positive on the whole prescribed
outer plateau, including its collar beyond the primitive support. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable (A : SmoothingAtlas M)

theorem phase_hessian_positive_of_outer (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {phi : SmallModes.Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (realPhaseChart e x).1 = phi x)
    {p : M} (hp : p ∈ (surfacePhaseChart (i : M) e).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1))
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
  have hI : Function.Injective (fderiv ℝ (A.realChartMap i F) (er.symm x)) := by
    rw [hback]
    exact A.realChartMap_injective_of_outer i hF hp.1 ho
  have hH := phase_chart_hessian_dy (A.realChartMap_smooth i hF.1) hphi hir x hcomp hI hdet
  have hmap : A.phaseRealChartMap i e.symm F = A.realChartMap i F ∘ er.symm := by
    funext y
    simp only [phaseRealChartMap,realChartMap,Function.comp_apply,er,realPhaseChart_symm_apply]
    have hb : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) = baseEquiv := rfl
    have hbs : (planeCoordinateIsometry.symm : SmallModes.Base → JetPolynomial.Base) = baseEquiv.symm := rfl
    rw [hb,hbs,baseEquiv.symm_apply_apply]
  rw [hmap,hH,hback,
    coordinateMetricHessian_congr_germ (A.realChartMap_metric_germ_of_outer i hF hp.1 ho)]
  apply hpositive
  have hI' := inverse_chart_derivative_injective er her hir hx
  intro hz
  have hh : (dy : SmallModes.Base) = 0 := hI' (hz.trans (map_zero _).symm)
  exact (show (dy : SmallModes.Base) ≠ 0 by simp [dy]) hh


end ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas

end

end OAI
