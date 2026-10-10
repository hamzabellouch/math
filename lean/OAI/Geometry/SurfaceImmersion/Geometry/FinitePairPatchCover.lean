import OAI.Geometry.SurfaceImmersion.Whitney.FixedSurfacePairPatch

namespace OAI

/-! A finite compact pair-patch cover outside prescribed diagonal
squares. All cutoffs are chosen before the surface maps are perturbed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem finite_pair_patch_cover {ι : Type*} [Fintype ι]
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {K : Set (M × M)} (hK : IsCompact K)
    (hne : ∀ z ∈ K, z.1 ≠ z.2)
    (hout : ∀ z ∈ K, ∀ i, ¬ (z.1 ∈ A i ∧ z.2 ∈ A i)) :
    ∃ (P : ∀ z : K, SurfacePairTranslationPatch z.val.1 z.val.2)
      (T : K → Set (M × M)) (s : Finset K),
      (∀ z, IsCompact (T z) ∧ T z ⊆ K ∩ ((P z).U ×ˢ (P z).V)) ∧
      (K ⊆ ⋃ z ∈ s, T z) ∧ ∀ z i,
        ((P z).χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ ((P z).χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
  classical
  have hex (z : K) : ∃ (P : SurfacePairTranslationPatch z.val.1 z.val.2)
      (T : Set (M × M)), IsCompact T ∧ z.val ∈ interior T ∧
      T ⊆ P.U ×ˢ P.V ∧ ∀ i,
      (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
    obtain ⟨P,hP⟩ := exists_fixed_surface_pair_patch A hA hdis z.val.1 z.val.2
      (hne z z.property) (hout z z.property)
    obtain ⟨T,hT,hzT,hTP⟩ := exists_compact_subset (P.openU.prod P.openV) ⟨P.memU,P.memV⟩
    exact ⟨P,T,hT,hzT,hTP,hP⟩
  choose P T hT hzT hTP hP using hex
  have hcover : K ⊆ ⋃ z : K, interior (T z) :=
    fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzT ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun z => interior (T z)) (fun _ => isOpen_interior) hcover
  refine ⟨P,fun z => K ∩ T z,s,?_,?_,hP⟩
  · intro z
    exact ⟨hK.inter (hT z),fun w hw => ⟨hw.1,hTP z hw.2⟩⟩
  · intro z hz
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hs hz)
    exact mem_iUnion₂.mpr ⟨i,hi,hz,interior_subset hzi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
