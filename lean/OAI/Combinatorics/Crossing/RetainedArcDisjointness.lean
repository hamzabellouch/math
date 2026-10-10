import OAI.Combinatorics.Crossing.RetainedDrawingArcs

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem arcs_pairwise_disjoint (C : DrawingPassages D) (p q : C.ArcIndex) (hpq : p ≠ q) :
    Disjoint (Set.range (C.arc p)) (Set.range (C.arc q)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxm := C.arc_avoids_marks p x hx
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  rw [C.arc_range] at hx hy
  obtain ⟨s,hs,hsx⟩ := hx
  obtain ⟨t,ht,htx⟩ := hy
  have hef : e=f := unmarked_intersection_same_edge D e f s t (hsx.trans htx.symm)
    (hsx.symm ▸ hxm)
  subst f
  have hst : s=t := D.edge_injective e (hsx.trans htx.symm)
  rw [← hst] at ht
  have hij : i ≠ j := by
    intro he
    subst j
    exact hpq rfl
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) i j hij) hs ht
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) j i hji) ht hs

end Zarankiewicz.DrawingPassages

end

end OAI
