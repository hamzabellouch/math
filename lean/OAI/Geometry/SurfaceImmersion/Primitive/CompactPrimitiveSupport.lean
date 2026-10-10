import OAI.Geometry.SurfaceImmersion.Atlas.PhaseDiskSupport
import OAI.Geometry.SurfaceImmersion.Atlas.SurfacePhaseCharts
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Exact compact support data for a primitive on an adapted analytic atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_primitive_support (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) {D : Set M} (hD : IsCompact D)
    (hDs : D ⊆ (surfacePhaseChart (i : M) e).source)
    (hactive : ∀ p ∈ D, A.weight i p ≠ 0) :
    ∃ K : Set JetPolynomial.Base, IsCompact K ∧ K ⊆ e.target ∧
      A.phaseSurfaceSupport i e K = D ∧
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) ∧
      (∀ p ∈ D, e (chart (i : M) p) ∈ K) ∧
      (∀ y ∈ K, A.chartWeight i (e.symm y) ≠ 0) ∧
      ∃ χ : JetPolynomial.Base → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ e.source ∧ ∀ x ∈ e.symm '' K, χ x = 1 := by
  let C := (chart (i : M)) '' D
  have hC : IsCompact C := hD.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hp => (hDs hp).1))
  have hCe : C ⊆ e.source := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hDs hp).2
  let K := e '' C
  have hK : IsCompact K := hC.image he.continuous
  have hinv : e.symm '' K = C := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [e.left_inv (hCe hz)] using hz
    · exact fun hx => ⟨e x,⟨x,hx,rfl⟩,e.left_inv (hCe hx)⟩
  refine ⟨K,hK,?_,?_,?_,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hCe hx)
  · exact A.phaseSurfaceSupport_image i e hD.isClosed
      (fun _ hp => (hDs hp).1) hCe
  · rw [hinv]
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨p,subset_tsupport _ (hactive p hp),rfl⟩
  · exact fun p hp => ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩
  · rintro y ⟨x,⟨p,hp,rfl⟩,rfl⟩
    have hpe : chart (i : M) p ∈ e.source := (hDs hp).2
    rw [e.left_inv hpe,chartWeight,
      indicator_of_mem ((chart (i : M)).map_source (hDs hp).1),
      (chart (i : M)).left_inv (hDs hp).1]
    exact hactive p hp
  · obtain ⟨χ,hχ,hχc,_,hχs,hχone⟩ := CollarVelocity.compact_cutoff hC e.open_source hCe
    exact ⟨χ,hχ,hχc,hχs,fun x hx => hχone x (hinv ▸ hx)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
