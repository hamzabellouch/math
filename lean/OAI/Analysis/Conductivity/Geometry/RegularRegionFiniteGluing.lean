import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma regularRegion_finite_gluing
    {I : Type*} [Fintype I]
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3} {U : Set Coord3}
    (O : I → Set Coord3) (hOU : ∀ i, O i ⊆ U)
    (hnew : ∀ i, RegularPatch v B (O i))
    (hu : EqOn v u (⋃ i, O i)ᶜ) (hA : EqOn B A (⋃ i, O i)ᶜ) :
    regularRegion u A U \ (⋃ i, frontier (O i)) ⊆ regularRegion v B U := by
  intro x hx
  by_cases hxi : x ∈ ⋃ i, O i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hxi
    exact mem_regularRegion_iff.mpr ⟨O i,hOU i,hnew i,hi⟩
  · obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx.1
    let W := V \ ⋃ i, closure (O i)
    have hclosed : IsClosed (⋃ i, closure (O i)) := isClosed_iUnion_of_finite (fun _ => isClosed_closure)
    have hW : IsOpen W := hV.1.sdiff hclosed
    have hxW : x ∈ W := by
      refine ⟨hxV,?_⟩
      intro hxc
      obtain ⟨i,hi⟩ := mem_iUnion.mp hxc
      apply hx.2
      refine mem_iUnion.mpr ⟨i,?_⟩
      rw [frontier, (hnew i).1.interior_eq]
      exact ⟨hi,fun hh => hxi (mem_iUnion.mpr ⟨i,hh⟩)⟩
    have hWoff : W ⊆ (⋃ i, O i)ᶜ := by
      intro y hy hi
      apply hy.2
      obtain ⟨i,hyi⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i,subset_closure hyi⟩
    exact mem_regularRegion_iff.mpr ⟨W,sdiff_subset.trans hVU,
      (hV.mono hW sdiff_subset).congr (hu.mono hWoff) (hA.mono hWoff),hxW⟩

lemma regularRegion_finite_gluing_ae
    (μ : Measure Coord3) {I : Type*} [Fintype I]
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3} {U : Set Coord3}
    (hold : μ (U \ regularRegion u A U) = 0)
    (O : I → Set Coord3) (hOU : ∀ i, O i ⊆ U)
    (hnew : ∀ i, RegularPatch v B (O i))
    (hu : EqOn v u (⋃ i, O i)ᶜ) (hA : EqOn B A (⋃ i, O i)ᶜ)
    (hnull : ∀ i, μ (frontier (O i)) = 0) :
    μ (U \ regularRegion v B U) = 0 := by
  have hs : U \ regularRegion v B U ⊆
      (U \ regularRegion u A U) ∪ (⋃ i, frontier (O i)) := by
    intro x hx
    by_cases hr : x ∈ regularRegion u A U
    · right
      by_contra hf
      exact hx.2 (regularRegion_finite_gluing O hOU hnew hu hA ⟨hr,hf⟩)
    · exact Or.inl ⟨hx.1,hr⟩
  exact measure_mono_null hs (measure_union_null hold (measure_iUnion_null hnull))

end ScalarConductivity

end

end OAI
