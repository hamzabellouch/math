import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionVectors

namespace OAI

/-! A curve's global second-form representative agrees with its transported
second form in the current primitive chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas

lemma curveSecondField_transition (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (β : SmallModes.Base → ℝ)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (j : M) f (i : M) e).source)
    (hwB : B.weight j ((surfacePhaseChart (j : M) f).symm x) ≠ 0)
    (hwA : A.weight i ((surfacePhaseChart (j : M) f).symm x) ≠ 0)
    (hβ : β x = 1) :
    let T := surfacePhaseTransition (j : M) f (i : M) e
    spaceCoordinates (B.phaseCurveSecondField j f β F (fun _ => dy) (fun _ => dy)
      ((surfacePhaseChart (j : M) f).symm x)) =
      realSecondForm (A.phaseRealChartMap i e.symm F)
        (fderiv ℝ T x dy) (fderiv ℝ T x dy) (T x) := by
  have hxj : x ∈ (surfacePhaseChart (j : M) f).target := hx.1
  have hp := (surfacePhaseChart (j : M) f).map_target hxj
  have hread := B.phaseCurveSecondField_eq j f β F (fun _ => dy) (fun _ => dy)
    hp.1 (B.outer_one j _ (subset_tsupport (B.weight j) hwB)) (by
      change β ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (j : M) f).symm x)) = 1
      rwa [(surfacePhaseChart (j : M) f).right_inv hxj])
  have hr : baseEquiv (f (chart (j : M) ((surfacePhaseChart (j : M) f).symm x))) = x :=
    (surfacePhaseChart (j : M) f).right_inv hxj
  simp only [hr] at hread
  rw [hread]
  exact B.phase_secondForm_transition A j i f e hf hfi he hi hF hx hwB hwA dy dy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
