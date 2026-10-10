import OAI.Geometry.SurfaceImmersion.Atlas.JetPhaseChartFromReal
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseBoundaryCurve

namespace OAI

/-! Phase charts for entire circular patches, chosen with a radius uniform
in the center and in a compact family of nonzero linear phase parameters. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem uniform_circular_phase_charts {P : Set Base} (hP : IsCompact P)
    (hP0 : ∀ ell ∈ P, ell ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : M) (ell : Base), ell ∈ P →
      ∃ e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base,
        ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
        (∀ x, (baseEquiv (e x)).1 = centeredConvexPhase ell L (coordinateChart q q) (baseEquiv x)) ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ R → ∀ x ∈ circularCoordinateRegion q r,
          baseEquiv.symm x ∈ e.source := by
  obtain ⟨R,hR,hcharts⟩ := compact_uniform_centered_charts hP hP0 hL
  refine ⟨R,hR,?_⟩
  intro q ell hell
  obtain ⟨e,hphase,he,hi,hcover⟩ := hcharts ell hell (coordinateChart q q)
  refine ⟨jetPhaseChart e,jetPhaseChart_smooth he,jetPhaseChart_symm_smooth hi,?_,?_⟩
  · intro x
    rw [jetPhaseChart_apply,baseEquiv.apply_symm_apply,hphase]
  · intro r hr hrR x hx
    rw [jetPhaseChart_source]
    change baseEquiv (baseEquiv.symm x) ∈ e.source
    rw [baseEquiv.apply_symm_apply]
    apply hcover
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact (circularRadiusSquared_le_norm hx).trans (by simpa only [abs_of_nonneg hr] using hrR)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
