import OAI.Combinatorics.Crossing.PolygonalArcInjective
import OAI.Combinatorics.Crossing.CompactCorridors

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_simple_polygonalChain {O : Set Plane} {a b : Plane} (hab : a ≠ b)
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, Function.Injective P.path ∧ Set.range P.path ⊆ O := by
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain h
  exact ⟨P,P.minimum_path_injective hab hmin,P.path_range_subset⟩

theorem finite_disjoint_polygonal_replacements {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → Plane) (hab : ∀ i, a i ≠ b i) (γ : ∀ i, Path (a i) (b i))
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)))
    (O : ι → Set Plane) (hO : ∀ i, IsOpen (O i))
    (hγ : ∀ i t, γ i t ∈ O i) :
    ∃ U : ι → Set Plane, ∃ P : ∀ i, PolygonalChain (U i) (a i) (b i),
      (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ O i) ∧
      (∀ i, Function.Injective (P i).path) ∧ (∀ i, Set.range (P i).path ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (P i).path) (Set.range (P j).path)) := by
  obtain ⟨U,hU,hKU,hUO,hUU⟩ := finite_compact_corridors (fun i => Set.range (γ i)) O
    (fun i => isCompact_range (γ i).continuous) hd hO (by
      intro i x hx
      obtain ⟨t,rfl⟩ := hx
      exact hγ i t)
  have hex (i : ι) : ∃ P : PolygonalChain (U i) (a i) (b i),
      Function.Injective P.path ∧ Set.range P.path ⊆ U i := by
    obtain ⟨P,hP,hR,_⟩ := exists_simple_polygonalChain_of_path (hab i) (γ i) (U i) (hU i)
      (fun t => hKU i ⟨t,rfl⟩)
    exact ⟨P,hP,hR⟩
  choose P hP hR using hex
  exact ⟨U,P,hU,hUO,hP,hR,fun i j hij => (hUU i j hij).mono (hR i) (hR j)⟩

end Zarankiewicz

end

end OAI
