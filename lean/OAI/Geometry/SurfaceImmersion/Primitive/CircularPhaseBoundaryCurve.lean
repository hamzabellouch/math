import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Primitive.CircularDiskTopology

namespace OAI

/-! Actual coordinate circles as the fixed phase curves of the induction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def circularPhaseBoundaryCurve (i : B.centers) {r r₀ : ℝ} (hr : 0 < r)
    (hsmall : r^2 < r₀^2)
    (hpos : ∀ p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) r₀)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    PhaseBoundaryCurve B where
  index := i
  phase := e
  smooth := he
  inverse_smooth := hi
  carrier := circularBoundary (i : M) r
  compact := circularBoundary_compact (i : M) hr hreg
  source := by
    intro p hp
    refine ⟨?_,?_⟩
    · change p ∈ (chart (i : M)).source
      rw [chart_source]
      simpa only [coordinateChart_source] using hp.1
    · have hx := hcover (coordinateChart (i : M) p) hp.2.le
      change baseEquiv.symm (baseEquiv (chart (i : M) p)) ∈ e.source at hx
      change chart (i : M) p ∈ e.source
      simpa only [baseEquiv.symm_apply_apply] using hx
  active := by
    intro p hp
    apply ne_of_gt ((hpos p).mpr ?_)
    exact ⟨hp.1,hp.2.trans_lt hsmall⟩

omit [CompactSpace M] in
@[simp] lemma circularPhaseBoundaryCurve_carrier (i : B.centers) {r r₀ : ℝ} (hr : 0 < r)
    (hsmall : r^2 < r₀^2)
    (hpos : ∀ p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) r₀)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    (B.circularPhaseBoundaryCurve i hr hsmall hpos hreg e he hi hcover).carrier =
      circularBoundary (i : M) r := rfl

omit [CompactSpace M] in
lemma circular_closed_disk_phase_source [T2Space M]
    (i : B.centers) {r : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    closure (circularCoordinateDisk (i : M) r) ⊆ (surfacePhaseChart (i : M) e).source := by
  rw [circularCoordinateDisk_closure (i : M) hr hreg]
  intro p hp
  obtain ⟨hs,hx⟩ := (circularDiskClosure_iff (i : M) hreg p).mp hp
  refine ⟨?_,?_⟩
  · change p ∈ (chart (i : M)).source
    rw [chart_source]
    simpa only [coordinateChart_source] using hs
  · have h := hcover (coordinateChart (i : M) p) hx
    change baseEquiv.symm (baseEquiv (chart (i : M) p)) ∈ e.source at h
    change chart (i : M) p ∈ e.source
    simpa only [baseEquiv.symm_apply_apply] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
