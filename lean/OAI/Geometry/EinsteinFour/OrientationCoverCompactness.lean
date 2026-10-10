import OAI.Geometry.EinsteinFour.OrientationCoverTopology
import Mathlib.Topology.Compactness.LocallyCompact

namespace OAI

/-! Compactness of the actual two-sheeted orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle Filter Topology
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_compact_orientationCover_neighborhood (x : M) :
    ∃ U ∈ 𝓝 x, ∃ K : Set (OrientationCover M), IsCompact K ∧
      ∀ y : OrientationCover M, y.proj ∈ U → y ∈ K := by
  let Z := orientationCoverCore (M := M)
  let e := Z.localTrivAt x
  obtain ⟨C, hCc, hCx, hCe⟩ := exists_compact_subset e.open_baseSet (Z.mem_localTrivAt_baseSet x)
  let K := e.toOpenPartialHomeomorph.symm '' (C ×ˢ (univ : Set Bool))
  have hK : IsCompact K := (hCc.prod isCompact_univ).image_of_continuousOn
    (e.toOpenPartialHomeomorph.continuousOn_symm.mono (by
      intro p hp
      exact e.mem_target.mpr (hCe hp.1)))
  refine ⟨C, mem_interior_iff_mem_nhds.mp hCx, K, hK, ?_⟩
  intro y hy
  have hs : y ∈ e.source := e.mem_source.mpr (hCe hy)
  refine ⟨e y, ?_, e.toOpenPartialHomeomorph.left_inv hs⟩
  have hp : (e y).1 = y.proj := e.proj_toFun y hs
  exact ⟨hp.symm ▸ hy, mem_univ _⟩

instance orientationCover_compactSpace : CompactSpace (OrientationCover M) := by
  choose U hU K hK hcover using exists_compact_orientationCover_neighborhood (M := M)
  obtain ⟨t, ht⟩ := finite_cover_nhds hU
  apply isCompact_univ_iff.mp
  have hc : IsCompact (⋃ x ∈ t, K x) :=
    t.finite_toSet.isCompact_biUnion (fun x _ => hK x)
  have heq : (⋃ x ∈ t, K x) = (univ : Set (OrientationCover M)) := by
    apply univ_subset_iff.mp
    intro y _
    have hy : y.proj ∈ ⋃ x ∈ t, U x := by rw [ht]; trivial
    obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x, hxt, hcover x y hx⟩
  rwa [heq] at hc

end
end PositiveEinsteinFour.Geometry

end OAI
