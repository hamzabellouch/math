import OAI.Geometry.SurfaceImmersion.Geometry.SubarcClosure

namespace OAI

/-! At an ordinary curve point, deleting the point from a sufficiently
small vertex-free neighborhood leaves two connected sides. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem line_punctured_neighborhood
    (c : OpenPartialHomeomorph X ℝ) {p : X} (hp : p ∈ c.source)
    (V : Set X) (hV : V.Finite) :
    ∃ W S T : Set X, IsOpen W ∧ p ∈ W ∧ IsConnected S ∧ IsConnected T ∧
      Disjoint S T ∧ W \ {p} = S ∪ T ∧ S ∪ T ⊆ Vᶜ ∧
      p ∈ closure S ∧ p ∈ closure T := by
  have hD : IsClosed (V \ {p}) := (hV.subset sdiff_subset).isClosed
  let U : Set X := (V \ {p})ᶜ
  have hU : IsOpen U := hD.isOpen_compl
  have hpU : p ∈ U := by rintro ⟨_,hn⟩; exact hn rfl
  let e := c.restrOpen U hU
  obtain ⟨A,W,hW,hpW,_,t,hlt,htr,htp,heq,hWe⟩ := line_chart_compact_arc_data e ⟨hp,hpU⟩
  let S := A.openSubarc A.left t.val
  let T := A.openSubarc t.val A.right
  have hsplit : W \ {p} = S ∪ T := by
    rw [heq]
    apply Subset.antisymm
    · rintro x ⟨⟨u,hu,rfl⟩,hne⟩
      have hut : u ≠ t := by intro h; apply hne; rw [h,htp]; rfl
      have hval : (u:ℝ) ≠ (t:ℝ) := fun h => hut (Subtype.ext h)
      rcases lt_or_gt_of_ne hval with h | h
      · exact Or.inl ⟨u,⟨hu.1,h⟩,rfl⟩
      · exact Or.inr ⟨u,⟨h,hu.2⟩,rfl⟩
    · intro x hx
      rcases hx with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
      · refine ⟨⟨u,⟨hu.1,hu.2.trans htr⟩,rfl⟩,?_⟩
        intro he
        have he' : A.map u = A.map t := by simpa only [mem_singleton_iff, htp] using he
        have hu' := congrArg Subtype.val (A.embedding.injective he')
        exact (ne_of_lt hu.2) hu'
      · refine ⟨⟨u,⟨hlt.trans hu.1,hu.2⟩,rfl⟩,?_⟩
        intro he
        have he' : A.map u = A.map t := by simpa only [mem_singleton_iff, htp] using he
        have hu' := congrArg Subtype.val (A.embedding.injective he')
        exact (ne_of_gt hu.1) hu'
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    rintro x ⟨s,hs,rfl⟩ ⟨u,hu,he⟩
    have heq := congrArg Subtype.val (A.embedding.injective he)
    linarith [hs.2,hu.1]
  refine ⟨W,S,T,hW,hpW,A.subarc_connected le_rfl htr.le hlt,
    A.subarc_connected hlt.le le_rfl htr,hdis,hsplit,?_,?_,?_⟩
  · intro x hx hxV
    have hxW := hsplit.symm ▸ hx
    exact (hWe hxW.1).2 ⟨hxV,hxW.2⟩
  · rw [show S = A.openSubarc A.left t.val from rfl,A.subarc_closure le_rfl htr.le hlt]
    exact ⟨t,⟨t.property.1,le_rfl⟩,htp⟩
  · rw [show T = A.openSubarc t.val A.right from rfl,A.subarc_closure hlt.le le_rfl htr]
    exact ⟨t,⟨le_rfl,t.property.2⟩,htp⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
