import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateIsometryMetric
import OAI.Geometry.SurfaceImmersion.Atlas.PreferredNormalPhasePullback

namespace OAI

/-! The fixed outer plateau, including points outside the partition weight,
retains the actual immersion, metric and normal in phase coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseRealChartMap_surface_germ_of_outer (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1)) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x] surfacePhaseMap (i : M) e F := by
  have hh := ho.comp_tendsto ((surfacePhaseChart (i : M) e).continuousAt_symm hx)
  filter_upwards [(surfacePhaseChart (i : M) e).open_target.mem_nhds hx,hh] with y hy hoy
  have hyt : e.symm (baseEquiv.symm y) ∈ (chart (i : M)).target := hy.2
  change spaceCoordinates (A.vectorChartRead i F (e.symm (baseEquiv.symm y))) =
    spaceCoordinates (F ((chart (i : M)).symm (e.symm (baseEquiv.symm y))))
  change A.outer i ((chart (i : M)).symm (e.symm (baseEquiv.symm y))) = 1 at hoy
  simp only [vectorChartRead,localize,indicator_of_mem hyt,hoy,one_pow,one_smul]

lemma realChartMap_germ_of_outer (i : A.centers) (F : M → Space) {p : M}
    (hp : p ∈ (chart (i : M)).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    A.realChartMap i F =ᶠ[𝓝 (coordinateChart (i : M) p)] coordinateMap F (i : M) := by
  let e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base := .refl _
  have hx : coordinateChart (i : M) p ∈ (surfacePhaseChart (i : M) e).target := by
    change (baseEquiv.symm (coordinateChart (i : M) p) ∈ Set.univ) ∧
      e.symm (baseEquiv.symm (coordinateChart (i : M) p)) ∈ (chart (i : M)).target
    refine ⟨mem_univ _,?_⟩
    rw [show coordinateChart (i : M) p = baseEquiv (chart (i : M) p) from rfl,
      baseEquiv.symm_apply_apply]
    exact (chart (i : M)).map_source hp
  have hback : (surfacePhaseChart (i : M) e).symm (coordinateChart (i : M) p) = p := by
    change (chart (i : M)).symm (baseEquiv.symm (coordinateChart (i : M) p)) = p
    rw [show coordinateChart (i : M) p = baseEquiv (chart (i : M) p) from rfl,
      baseEquiv.symm_apply_apply,(chart (i : M)).left_inv hp]
  have hh := A.phaseRealChartMap_surface_germ_of_outer i e F hx (by rwa [hback])
  exact hh

lemma realChartMap_metric_germ_of_outer (i : A.centers) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M}
    (hp : p ∈ (chart (i : M)).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    inducedCoordinateMetric (A.realChartMap i F) =ᶠ[𝓝 (coordinateChart (i : M) p)]
      coordinateMetric g (i : M) := by
  have hg := A.realChartMap_germ_of_outer i F hp ho
  have hpc : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using hp
  have hpt : coordinateChart (i : M) p ∈ coordinateDomain (i : M) := by
    rw [← coordinateChart_target]
    exact (coordinateChart (i : M)).map_source hpc
  filter_upwards [hg.eventuallyEq_nhds,(coordinateDomain_open (i : M)).mem_nhds hpt] with y hy hyt
  rw [← coordinateMap_metric hF (i : M) hyt]
  simp only [inducedCoordinateMetric,realMetric,coordDeriv,hy.fderiv_eq]

lemma realChartMap_injective_of_outer (i : A.centers) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M}
    (hp : p ∈ (chart (i : M)).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    Function.Injective (fderiv ℝ (A.realChartMap i F) (coordinateChart (i : M) p)) := by
  rw [(A.realChartMap_germ_of_outer i F hp ho).fderiv_eq]
  apply coordinateMap_injective_of_immersion hF.1 (IsSmoothIsometricImmersion.mfderiv_injective hF)
  rw [← coordinateChart_target]
  apply (coordinateChart (i : M)).map_source
  simpa only [coordinateChart_source,chart_source] using hp

lemma preferred_normal_in_phase_of_outer (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {x : SmallModes.Base}
    (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1))
    (v : SmallModes.Base) :
    coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 := by
  rw [coordDeriv,(A.phaseRealChartMap_surface_germ_of_outer i e F hx ho).fderiv_eq]
  exact n.inPhase_normal hF (i : M) e hi hx v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
