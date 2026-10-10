import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonClosedCover
open Set

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

theorem graph_reachable_cover (G : SimpleGraph ι) (C : ι → Set X)
    (hclosed : ∀ i,IsClosed (C i))
    (hconn : IsPreconnected (⋃ i,C i)) (hne : ∀ i,(C i).Nonempty)
    (hadj : ∀ i j,(C i∩C j).Nonempty → G.Reachable i j) : G.Preconnected := by
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
  obtain ⟨z,-,hzU,hzV⟩ := isPreconnected_closed_iff.mp hconn U V hU hV hsub
    ⟨x,mem_iUnion.mpr ⟨a,hx⟩,mem_iUnion.mpr ⟨⟨a,.rfl⟩,hx⟩⟩
    ⟨y,mem_iUnion.mpr ⟨b,hy⟩,mem_iUnion.mpr ⟨⟨b,hb⟩,hy⟩⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzU
  obtain ⟨j,hj⟩ := mem_iUnion.mp hzV
  exact j.property (i.property.trans (hadj _ _ ⟨z,hi,hj⟩))

omit [Finite ι] in
theorem union_preconnected (G : SimpleGraph ι) (hG : G.Preconnected)
    (C : ι → Set X) (hc : ∀ i,IsPreconnected (C i)) (hne : ∀ i,(C i).Nonempty)
    (hadj : ∀ i j,G.Adj i j → (C i∩C j).Nonempty) : IsPreconnected (⋃ i,C i) := by
  classical
  choose z hz using hne
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hconst (i : ι) {x y : X} (hx:x∈C i) (hy:y∈C i) : f x=f y :=
    (hc i).constant (hf.mono (subset_iUnion C i)) hx hy
  have hstep (i j:ι) (hij:G.Adj i j) : f (z i)=f (z j) := by
    obtain ⟨w,hwi,hwj⟩ := hadj i j hij
    exact (hconst i (hz i) hwi).trans (hconst j hwj (hz j))
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp hy
  have hwalk {a b:ι} (p:G.Walk a b) : f (z a)=f (z b) := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (hstep _ _ h).trans ih
  obtain ⟨p⟩ := hG i j
  exact (hconst i hi (hz i)).trans ((hwalk p).trans (hconst j (hz j) hj))
end CannonClosedCover

end
end
end
end

end OAI
