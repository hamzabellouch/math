import OAI.Geometry.SurfaceImmersion.Whitney.GlobalPairRegularization

namespace OAI

/-! Construct the quantitative injectivity cover before regularizing
all double pairs on the surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι]

theorem relative_global_transversality
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (A U : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hU : ∀ i, IsOpen (U i)) (hUA : ∀ i, U i ⊆ A i)
    (hIf : ∀ x, x ∉ ⋃ i, U i → Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hAreg : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ regularSurfacePairs f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      ∀ x y, x ≠ y → g x = g y → Function.Surjective (surfacePairDerivative g x y) := by
  classical
  let B : Set M := (⋃ i, U i)ᶜ
  have hB : IsCompact B := (isOpen_iUnion hU).isClosed_compl.isCompact
  obtain ⟨P,s,hs⟩ := finite_injectivity_cover hf hB hIf
  let c : s → M := fun j => j.val.val
  let Q : ∀ j : s, SurfaceInjectivityPatch f (c j) := fun j => P j.val
  have hcover : (⋃ i, U i) ∪ (⋃ j : s, (Q j).region) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · exact Or.inl hx
    · obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hs hx)
      exact Or.inr (mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩)
  exact global_pair_regularization_with_cover hf A U hA hdis hU hUA hIf hAreg c Q hcover hε

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
