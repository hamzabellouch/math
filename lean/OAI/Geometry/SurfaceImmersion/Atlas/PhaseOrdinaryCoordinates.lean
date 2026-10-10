import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCurvePairGeometry

namespace OAI

/-! The identity phase recovers ordinary surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates RealModes SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma surfacePhaseChart_refl_apply (q p : M) :
    surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base) p = coordinateChart q p := rfl

lemma surfacePhaseChart_refl_symm_apply (q : M) (x : SmallModes.Base) :
    (surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).symm x =
      (coordinateChart q).symm x := by
  simp [surfacePhaseChart_symm_apply,FiniteOrderSmoothing.chart,coordinateChart_symm_apply,
    coordinateInverse,planeModel,baseEquiv,planeCoordinates]

lemma surfacePhaseChart_refl_source (q : M) :
    (surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).source =
      (coordinateChart q).source := by
  simp [surfacePhaseChart,FiniteOrderSmoothing.chart,coordinateChart]

lemma surfacePhaseMap_refl (q : M) (F : M → Space) :
    surfacePhaseMap q (OpenPartialHomeomorph.refl JetPolynomial.Base) F = coordinateMap F q := by
  funext x
  simp only [surfacePhaseMap,Function.comp_apply,surfacePhaseChart_refl_symm_apply,
    coordinateChart_symm_apply]
  rfl

end ClosedSurfaceR4

end

end OAI
