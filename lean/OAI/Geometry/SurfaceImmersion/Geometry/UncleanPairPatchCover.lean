import OAI.Geometry.SurfaceImmersion.Geometry.FinitePairPatchCover
import OAI.Geometry.SurfaceImmersion.Whitney.CleanSurfacePairs

namespace OAI

/-! Cover only pairs that fail transversality or finite-point avoidance;
the compact remainder already satisfies both properties. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι]

theorem unclean_pair_patch_cover
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {K : Set (M × M)} (hK : IsCompact K) (hne : ∀ z ∈ K, z.1 ≠ z.2)
    (S : Set M) (hS : S.Finite)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hAreg : ∀ z ∈ K, (∃ i, z.1 ∈ A i ∧ z.2 ∈ A i) → z ∈ cleanSurfacePairs f S) :
    let D := K \ cleanSurfacePairs f S
    ∃ (P : ∀ z : D, SurfacePairTranslationPatch z.val.1 z.val.2)
      (T : D → Set (M × M)) (s : Finset D) (J : Set (M × M)),
      (∀ z, IsCompact (T z) ∧ T z ⊆ (P z).U ×ˢ (P z).V) ∧
      (∀ z i, ((P z).χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨
        ((P z).χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1))) ∧
      IsCompact J ∧ J ⊆ cleanSurfacePairs f S ∧ K ⊆ J ∪ ⋃ z ∈ s, T z := by
  classical
  dsimp only
  let D := K \ cleanSurfacePairs f S
  have hD : IsCompact D := hK.diff (cleanSurfacePairs_open hf hS)
  have hex (z : D) : ∃ (P : SurfacePairTranslationPatch z.val.1 z.val.2)
      (T : Set (M × M)), IsCompact T ∧ z.val ∈ interior T ∧
      T ⊆ P.U ×ˢ P.V ∧ ∀ i,
      (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
    have hout : ∀ i, ¬ (z.val.1 ∈ A i ∧ z.val.2 ∈ A i) := by
      intro i hi
      exact z.property.2 (hAreg z z.property.1 ⟨i,hi⟩)
    obtain ⟨P,hP⟩ := exists_fixed_surface_pair_patch A hA hdis z.val.1 z.val.2
      (hne z z.property.1) hout
    obtain ⟨T,hT,hzT,hTP⟩ := exists_compact_subset (P.openU.prod P.openV) ⟨P.memU,P.memV⟩
    exact ⟨P,T,hT,hzT,hTP,hP⟩
  choose P T hT hzT hTP hP using hex
  have hcover : D ⊆ ⋃ z : D, interior (T z) :=
    fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzT ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hD.elim_finite_subcover (fun z => interior (T z)) (fun _ => isOpen_interior) hcover
  let J := K \ ⋃ z ∈ s, interior (T z)
  have hJ : IsCompact J := hK.diff (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_interior)
  have hJgood : J ⊆ cleanSurfacePairs f S := by
    intro z hz
    by_contra hbad
    exact hz.2 (hs ⟨hz.1,hbad⟩)
  refine ⟨P,T,s,J,fun z => ⟨hT z,hTP z⟩,hP,hJ,hJgood,?_⟩
  intro z hz
  by_cases hu : z ∈ ⋃ i ∈ s, interior (T i)
  · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hu
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,interior_subset hzi⟩)
  · exact Or.inl ⟨hz,hu⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
