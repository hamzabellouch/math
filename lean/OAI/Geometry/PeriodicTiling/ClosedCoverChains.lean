import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Logic.Relation

namespace OAI

universe uX uI

namespace PeriodicTilingThree

open Set MeasureTheory

section Topological

variable {X : Type uX} {I : Type uI} [TopologicalSpace X] [PreconnectedSpace X]

def CoverIntersects (K : I → Set X) (i j : I) : Prop :=
  (K i ∩ K j).Nonempty

theorem closed_cover_chain_connected (K : I → Set X)
    (hne : ∀ i, (K i).Nonempty) (hclosed : ∀ i, IsClosed (K i))
    (hlocal : LocallyFinite K) (hcover : ∀ x : X, ∃ i, x ∈ K i)
    (i₀ j : I) : Relation.ReflTransGen (CoverIntersects K) i₀ j := by
  classical
  let R : I → Prop := Relation.ReflTransGen (CoverIntersects K) i₀
  let A : Set X := ⋃ i : {i // R i}, K i.val
  let B : Set X := ⋃ i : {i // ¬ R i}, K i.val
  have hA : IsClosed A :=
    (hlocal.comp_injective (g := fun i : {i // R i} => i.val)
      Subtype.val_injective).isClosed_iUnion (fun i => hclosed i.val)
  have hB : IsClosed B :=
    (hlocal.comp_injective (g := fun i : {i // ¬ R i} => i.val)
      Subtype.val_injective).isClosed_iUnion (fun i => hclosed i.val)
  have hab : (univ : Set X) ⊆ A ∪ B := by
    intro x _
    obtain ⟨i, hxi⟩ := hcover x
    by_cases hi : R i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  have hAnonempty : ((univ : Set X) ∩ A).Nonempty := by
    obtain ⟨x, hx⟩ := hne i₀
    exact ⟨x, mem_univ x,
      mem_iUnion.mpr ⟨⟨i₀, Relation.ReflTransGen.refl⟩, hx⟩⟩
  by_contra hj
  have hBnonempty : ((univ : Set X) ∩ B).Nonempty := by
    obtain ⟨x, hx⟩ := hne j
    exact ⟨x, mem_univ x, mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩⟩
  obtain ⟨x, _, hxA, hxB⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_univ A B hA hB hab hAnonempty hBnonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hxB
  exact k.property (i.property.tail ⟨x, hxi, hxk⟩)

end Topological

section Measure

variable {X : Type uX} {I : Type uI} [TopologicalSpace X] [MeasurableSpace X]
variable (μ : Measure X) [MeasureTheory.Measure.IsOpenPosMeasure μ]

theorem closed_locallyFinite_cover_of_ae (K : I → Set X)
    (hclosed : ∀ i, IsClosed (K i)) (hlocal : LocallyFinite K)
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ K i) : ∀ x, ∃ i, x ∈ K i := by
  have hc : IsClosed (⋃ i, K i) := hlocal.isClosed_iUnion hclosed
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ i, K i :=
    hcover.mono fun _ hx => mem_iUnion.mpr hx
  have hnull : μ (⋃ i, K i)ᶜ = 0 := mem_ae_iff.mp hae
  have hempty : (⋃ i, K i)ᶜ = ∅ :=
    (hc.isOpen_compl.measure_eq_zero_iff μ).mp hnull
  have huniv : (⋃ i, K i) = univ := Set.compl_empty_iff.mp hempty
  intro x
  exact mem_iUnion.mp (by rw [huniv]; exact mem_univ x)

end Measure

end PeriodicTilingThree

end OAI
