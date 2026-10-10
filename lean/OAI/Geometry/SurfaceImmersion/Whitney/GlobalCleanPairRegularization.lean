import OAI.Geometry.SurfaceImmersion.Whitney.CompactCleanPairRegularization
import OAI.Geometry.SurfaceImmersion.Geometry.FrozenCleanPairs
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteInjectivityCover
import OAI.Geometry.SurfaceImmersion.Geometry.FrozenPairGeometry

namespace OAI

/-! Global regularization with a fixed injectivity cover and frozen
crosscap neighborhoods. No distinct double pair is left uncontrolled. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι ν : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι] [Fintype ν]

theorem global_clean_pair_regularization_with_cover
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (A U : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hU : ∀ i, IsOpen (U i)) (hUA : ∀ i, U i ⊆ A i)
    (hIf : ∀ x, x ∉ ⋃ i, U i → Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (S : Set M) (hS : S.Finite)
    (hAclean : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S)
    (c : ν → M) (P : ∀ j, SurfaceInjectivityPatch f (c j))
    (hcover : (⋃ i, U i) ∪ (⋃ j, (P j).region) = univ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      ∀ x y, x ≠ y → (x,y) ∈ cleanSurfacePairs g S := by
  classical
  let B : Set M := (⋃ i, U i)ᶜ
  have hB : IsCompact B := (isOpen_iUnion hU).isClosed_compl.isCompact
  let W : Set (M × M) := (⋃ i, U i ×ˢ U i) ∪ (⋃ j, (P j).region ×ˢ (P j).region)
  let K : Set (M × M) := Wᶜ
  have hW : IsOpen W := (isOpen_iUnion fun i => (hU i).prod (hU i)).union
    (isOpen_iUnion fun j => (P j).region_open.prod (P j).region_open)
  have hK : IsCompact K := hW.isClosed_compl.isCompact
  have hne : ∀ z ∈ K, z.1 ≠ z.2 := by
    rintro ⟨x,y⟩ hz hxy
    have hx : x ∈ (⋃ i, U i) ∪ ⋃ j, (P j).region := by rw [hcover]; trivial
    apply hz
    rcases hx with hx | hx
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact Or.inl (mem_iUnion.mpr ⟨i,hi,hxy ▸ hi⟩)
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨j,hj,hxy ▸ hj⟩)
  let Q : ν → Set Base := fun j => Metric.closedBall (chart (c j) (c j)) (P j).radius
  have hsmall (s : Finset ν) : ∃ η > 0, η ≤ ε ∧ ∀ j ∈ s, η ≤ 1/(4*((P j).K:ℝ)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨ε,hε,le_rfl,by simp⟩
    | @insert j s hj ih =>
      obtain ⟨η,hη,hηε,hηs⟩ := ih
      have hp : 0 < 1/(4*((P j).K:ℝ)) := by have := (P j).K_pos; positivity
      refine ⟨min η (1/(4*((P j).K:ℝ))),lt_min hη hp,(min_le_left _ _).trans hηε,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hηs k hk)
  obtain ⟨η,hη,hηε,hηP⟩ := hsmall Finset.univ
  obtain ⟨g,hg,hfg,hclose,hD,hIg,hgood⟩ := compact_relative_clean_pair_regularization A hA hdis hK hne S hS
    c Q (fun j => isCompact_closedBall _ _) (fun j => (P j).target)
    B hB hf hIf
    (by rintro z hz ⟨i,hix,hiy⟩; exact hAclean i z.1 hix z.2 hiy (hne z hz)) hη
  have hIpatch (j : ν) : InjOn g (P j).region := (P j).injective_of_close hg
    (fun y hy => (hD j y hy).trans_le (hηP j (Finset.mem_univ j)))
  have hBA : B ∪ ⋃ i, A i = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,hUA i hi⟩)
    · exact Or.inl hx
  refine ⟨g,hg,hfg,fun x => (hclose x).trans_le hηε,
    frozen_immersion_equivalence hBA hf hfg hIf hIg,?_⟩
  intro x y hxy
  by_cases hxyK : (x,y) ∈ K
  · exact hgood hxyK
  have hxyW : (x,y) ∈ W := by simpa only [K,mem_compl_iff,not_not] using hxyK
  rcases hxyW with hu | hp
  · obtain ⟨i,hxi,hyi⟩ := mem_iUnion.mp hu
    exact hfg.clean_pair hf S i (hUA i hxi) (hUA i hyi)
      (hAclean i x (hUA i hxi) y (hUA i hyi) hxy)
  · obtain ⟨j,hxj,hyj⟩ := mem_iUnion.mp hp
    apply mem_cleanSurfacePairs.mpr
    intro hgeq
    exact False.elim (hxy (hIpatch j hxj hyj hgeq))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
