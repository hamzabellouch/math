import OAI.Geometry.SurfaceImmersion.Geometry.UncleanPairPatchCover
import OAI.Geometry.SurfaceImmersion.Whitney.FiniteCleanPairRegularization

namespace OAI

/-! Relative transversality on compact pair sets, including sets that
meet the frozen crosscap neighborhoods. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι ν : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι] [Fintype ν]

theorem compact_relative_clean_pair_regularization
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {K : Set (M × M)} (hK : IsCompact K) (hne : ∀ z ∈ K, z.1 ≠ z.2)
    (S : Set M) (hS : S.Finite)
    (c : ν → M) (Q : ν → Set Base) (hQ : ∀ j, IsCompact (Q j))
    (hQT : ∀ j, Q j ⊆ (chart (c j)).target)
    (B : Set M) (hB : IsCompact B)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hAreg : ∀ z ∈ K, (∃ i, z.1 ∈ A i ∧ z.2 ∈ A i) → z ∈ cleanSurfacePairs f S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      ChartDerivativeClose c Q f g ε ∧
      (∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) ∧
      K ⊆ cleanSurfacePairs g S := by
  obtain ⟨P,T,s,J,hT,hPA,hJ,hJreg,hcover⟩ := unclean_pair_patch_cover A hA hdis hK hne S hS hf hAreg
  obtain ⟨g,hg,hfg,hclose,hD,hI,hJg,hgood⟩ := finite_surface_pair_clean_relative
    (fun z : {z : M × M // z ∈ K ∧ z ∉ cleanSurfacePairs f S} => z.val.1)
    (fun z : {z : M × M // z ∈ K ∧ z ∉ cleanSurfacePairs f S} => z.val.2) P T
    (fun z => (hT z).1) (fun z => (hT z).2) A hPA S hS J hJ c Q hQ hQT s B hB hf hIf
    hJreg hε
  refine ⟨g,hg,hfg,hclose,hD,hI,?_⟩
  intro z hz
  rcases hcover hz with hz | hz
  · exact hJg hz
  · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz
    exact hgood i hi hzi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
