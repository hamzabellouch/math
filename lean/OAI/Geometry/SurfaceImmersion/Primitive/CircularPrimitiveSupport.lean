import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseDiskSupport
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! The exact analytic compact support and cutoff of a geometric circular
primitive. In particular the support is the closed disk, not the atlas patch. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem circular_primitive_support (i : A.centers) {r r₀ : ℝ} (hr : 0 < r)
    (hsmall : r^2 < r₀^2)
    (hpos : ∀ p, 0 < A.weight i p ↔ p ∈ circularCoordinateDisk (i : M) r₀)
    (hreg : circularCoordinateRegion (i : M) r ⊆ (coordinateChart (i : M)).target)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (he : ContDiff ℝ ∞ e)
    (hcover : ∀ x ∈ circularCoordinateRegion (i : M) r, baseEquiv.symm x ∈ e.source) :
    ∃ K : Set JetPolynomial.Base, IsCompact K ∧ K ⊆ e.target ∧
      A.phaseSurfaceSupport i e K = closure (circularCoordinateDisk (i : M) r) ∧
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) ∧
      ∃ χ : JetPolynomial.Base → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ e.source ∧ ∀ x ∈ e.symm '' K, χ x = 1 := by
  let D := circularDiskClosure (i : M) r
  have hD : IsCompact D := circularDiskClosure_compact (i : M) r hreg
  have hsource : D ⊆ (surfacePhaseChart (i : M) e).source := by
    dsimp only [D]
    rw [← circularCoordinateDisk_closure (i : M) hr hreg]
    exact A.circular_closed_disk_phase_source i hr hreg e hcover
  have hDs : D ⊆ (chart (i : M)).source := fun _ hp => (hsource hp).1
  have hDe : (chart (i : M)) '' D ⊆ e.source := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hsource hp).2
  let C := (chart (i : M)) '' D
  have hC : IsCompact C := hD.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono hDs)
  let K := e '' C
  have hK : IsCompact K := hC.image he.continuous
  have heC : e.symm '' K = C := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [e.left_inv (hDe hz)] using hz
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.left_inv (hDe hx)⟩
  refine ⟨K,hK,?_,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hDe hx)
  · rw [A.phaseSurfaceSupport_image i e hD.isClosed hDs hDe]
    exact (circularCoordinateDisk_closure (i : M) hr hreg).symm
  · rw [heC]
    rintro _ ⟨p,hp,rfl⟩
    have hp' := (circularDiskClosure_iff (i : M) hreg p).mp hp
    have hw : A.weight i p ≠ 0 := ne_of_gt ((hpos p).mpr ⟨hp'.1,hp'.2.trans_lt hsmall⟩)
    exact ⟨p,subset_tsupport (A.weight i) hw,rfl⟩
  · obtain ⟨χ,hχ,hχc,_,hχs,hχone⟩ := CollarVelocity.compact_cutoff hC e.open_source hDe
    exact ⟨χ,hχ,hχc,hχs,fun x hx => hχone x (heC ▸ hx)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
