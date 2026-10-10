import OAI.Geometry.SurfaceImmersion.Primitive.PrimitivePatchCurves
import OAI.Geometry.SurfaceImmersion.Atlas.RestrictedPhaseTransition
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseCurveCrossings

namespace OAI

/-! Transfer the actual old boundary invariant to the new analytic patch.
The source restriction preserves the current primitive's vertical direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch
variable (d : SupportedPrimitivePatch A i e F amp phi D)

omit [T2Space M] in
include d in
lemma current_second (c₀ : PhaseBoundaryCurve B)
    (hi : (i : M) = (c₀.index : M)) (he : ∀ x, e x = c₀.phase x)
    {g : SmoothMetric M} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hp : p ∈ c₀.carrier) (hpD : p ∈ closure D) :
    c₀.second F p = realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
      (surfacePhaseChart (i : M) e p) := by
  have hs := c₀.second_transition A i e d.phase_smooth d.inverse_smooth hF hp
    (d.source_closed hpD) (d.active_closed p hpD)
  have ht := same_phase_transition_fderiv (c₀.index : M) (i : M) hi.symm c₀.phase e he (c₀.source hp)
  change fderiv ℝ (surfacePhaseTransition (c₀.index : M) c₀.phase (i : M) e)
    (c₀.coordinate p) = ContinuousLinearMap.id ℝ Base at ht
  dsimp only at hs
  rw [ht,ContinuousLinearMap.id_apply] at hs
  exact hs

omit [T2Space M] in
lemma zero_amplitude_frontier (c : PhaseBoundaryCurve B) (hD : IsOpen D)
    {p : M} (hp : p ∈ c.carrier ∩ closure D)
    (ha : d.amplitude (surfacePhaseChart (i : M) e p) = 0) : p ∈ frontier D := by
  refine ⟨hp.2,?_⟩
  rw [hD.interior_eq]
  intro hpin
  have hpos := (d.amplitude_positive _).mpr ⟨p,hpin,rfl⟩
  rw [ha] at hpos
  exact lt_irrefl _ hpos

omit [T2Space M] in
lemma old_boundary_crossing (c₀ c : PhaseBoundaryCurve B)
    (hi : (i : M) = (c₀.index : M)) (he : ∀ x, e x = c₀.phase x)
    (hD : IsOpen D) (hfront : c₀.carrier = frontier D)
    {g : SmoothMetric M} (hF : IsSmoothIsometricImmersion M g F)
    (b k : Base → ℝ)
    (hv : ∀ p ∈ c.carrier ∩ closure D,
      (b (surfacePhaseChart (i : M) e p),k (surfacePhaseChart (i : M) e p)) =
        fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy)
    (hpositive : ∀ p ∈ c.carrier ∩ frontier D, 0 < c₀.crossing c F p) :
    ∀ x ∈ d.curve c, d.amplitude x = 0 →
      0 < orderedCrossing (A.phaseRealChartMap i e.symm F) dy (b x,k x) x
        (coordinateGaussianCurvature (realMetric (A.phaseRealChartMap i e.symm F) dx dx)
          (realMetric (A.phaseRealChartMap i e.symm F) dx dy)
          (realMetric (A.phaseRealChartMap i e.symm F) dy dy) x) := by
  rintro x ⟨p,hp,rfl⟩ ha
  have hpf := d.zero_amplitude_frontier c hD hp ha
  have hp₀ : p ∈ c₀.carrier := hfront.symm ▸ hpf
  have hcross := c₀.crossing_transition c A i e d.phase_smooth d.inverse_smooth hF hp₀ hp.1
    (d.source_closed hp.2) (d.active_closed p hp.2)
  have ht := same_phase_transition_fderiv (c₀.index : M) (i : M) hi.symm c₀.phase e he (c₀.source hp₀)
  change fderiv ℝ (surfacePhaseTransition (c₀.index : M) c₀.phase (i : M) e)
    (c₀.coordinate p) = ContinuousLinearMap.id ℝ Base at ht
  dsimp only at hcross
  rw [ht,ContinuousLinearMap.id_apply,← hv p hp] at hcross
  have hc := hpositive p ⟨hp.1,hpf⟩
  rw [hcross] at hc
  exact hc

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
