import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts
import OAI.Geometry.SurfaceImmersion.Geometry.CurveSecondFields

namespace OAI

/-! Exterior comparison regions in the actual phase chart, including their
boundary points. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def phaseExteriorDomain (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (O : Set M) :
    Set JetPolynomial.Base :=
  ((chart q).trans e) '' (O ∩ ((chart q).trans e).source)

lemma phaseExteriorDomain_properties (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (O : Set M) :
    ∀ y ∈ phaseExteriorDomain q e O,
      e.symm y ∈ (chart q).target ∧ (chart q).symm (e.symm y) ∈ O := by
  rintro y ⟨p,⟨hpO,hps⟩,rfl⟩
  have hpe : chart q p ∈ e.source := hps.2
  have he := e.left_inv hpe
  change e.symm (e (chart q p)) ∈ (chart q).target ∧
    (chart q).symm (e.symm (e (chart q p))) ∈ O
  rw [he,(chart q).left_inv hps.1]
  exact ⟨(chart q).map_source hps.1,hpO⟩

lemma phaseExteriorDomain_closure (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (O : Set M)
    {p : M} (hps : p ∈ ((chart q).trans e).source) (hpO : p ∈ closure O) :
    e (chart q p) ∈ closure (phaseExteriorDomain q e O) := by
  have hc : ContinuousAt ((chart q).trans e) p := ((chart q).trans e).continuousAt hps
  exact mem_closure_image hc (((chart q).trans e).open_source.closure_inter ⟨hpO,hps⟩)

namespace SmoothingAtlas
variable [IsManifold planeModel ∞ M] [CompactSpace M] (A : SmoothingAtlas M)

lemma phase_gram_at_source (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hp : p ∈ ((chart (i : M)).trans e).source) (hw : A.weight i p ≠ 0) :
    NormalFrame.gramDet
      (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p))))
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p)))) ≠ 0 := by
  have hpe : chart (i : M) p ∈ e.source := hp.2
  apply A.phase_gram_ne_zero i e he hi hF
  · simpa only [baseEquiv.symm_apply_apply] using e.map_source hpe
  · rw [baseEquiv.symm_apply_apply,e.left_inv hpe,chartWeight,
      indicator_of_mem ((chart (i : M)).map_source hp.1),(chart (i : M)).left_inv hp.1]
    exact hw

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
