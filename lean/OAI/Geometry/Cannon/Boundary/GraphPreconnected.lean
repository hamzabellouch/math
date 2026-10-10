import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonClosedCover
open Set

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

theorem graph_preconnected (G : SimpleGraph ι) (C : ι → Set X)
    (hclosed : ∀ i,IsClosed (C i))
    (hconn : IsPreconnected (⋃ i,C i)) (hne : ∀ i,(C i).Nonempty)
    (hadj : ∀ i j,i≠j → (C i∩C j).Nonempty → G.Adj i j) : G.Preconnected := by
  classical
  intro a b
  by_contra hb
  let U : Set X := ⋃ i : {i : ι | G.Reachable a i},C i.val
  let V : Set X := ⋃ i : {i : ι | ¬G.Reachable a i},C i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite fun i=>hclosed i.val
  have hV : IsClosed V := isClosed_iUnion_of_finite fun i=>hclosed i.val
  have hsub : (⋃ i,C i)⊆U∪V := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases h : G.Reachable a i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
  obtain ⟨x,hx⟩ := hne a
  obtain ⟨y,hy⟩ := hne b
  obtain ⟨z,hz,hzU,hzV⟩ := isPreconnected_closed_iff.mp hconn U V hU hV hsub
    ⟨x,mem_iUnion.mpr ⟨a,hx⟩,mem_iUnion.mpr ⟨⟨a,.rfl⟩,hx⟩⟩
    ⟨y,mem_iUnion.mpr ⟨b,hy⟩,mem_iUnion.mpr ⟨⟨b,hb⟩,hy⟩⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzU
  obtain ⟨j,hj⟩ := mem_iUnion.mp hzV
  have hneij : i.val≠j.val := fun h=>j.property (h ▸ i.property)
  exact j.property (i.property.trans (hadj _ _ hneij ⟨z,hi,hj⟩).reachable)
end CannonClosedCover

end
end
end
end

end OAI
