import OAI.Geometry.SurfaceImmersion.Atlas.AtlasOuterPlateau

namespace OAI

/-! Choose the analytic atlas patch with both its weight support and its
outer plateau prescribed by the primitive's compact neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_smoothingAtlas_prescribed_plateau (q : M) {K U P : Set M}
    (hK : IsCompact K) (hqK : q ∈ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUs : U ⊆ (chart q).source) (hP : IsCompact P) (hPs : P ⊆ (chart q).source) :
    ∃ (A : SmoothingAtlas M) (i : A.centers), (i : M) = q ∧
      (∀ p ∈ K, 0 < A.weight i p) ∧ tsupport (A.weight i) ⊆ U ∧
      (∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1)) ∧
      ∀ p ∈ P, A.outer i =ᶠ[𝓝 p] (fun _ => 1) := by
  obtain ⟨A,i,hiq,hpos,hsupp,_hnon,ho⟩ := exists_smoothingAtlas_prescribed_patch q hK hqK hU hKU hUs
  have hPs' : P ⊆ (chart (i : M)).source := by simpa only [hiq] using hPs
  obtain ⟨B,hcenters,hw,hout,hplateau⟩ := A.enlarge_outer_plateau i hP hPs' ho
  have hcast {s t : Finset M} (h : s = t) (j : s) :
      ((h ▸ j : t) : M) = (j : M) := by
    subst t
    rfl
  refine ⟨B,hcenters.symm ▸ i,(hcast hcenters.symm i).trans hiq,?_,?_,hout,hplateau⟩
  · intro p hp
    rw [hw]
    exact hpos p hp
  · have he : B.weight (hcenters.symm ▸ i) = A.weight i := funext (hw i)
    rwa [he]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
