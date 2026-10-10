import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.FaceClosuresCover
import OAI.Geometry.Cannon.PlaneTopology.FreeArcDeleteConnected

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
noncomputable section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem face_vertices_card_three (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcard : 3≤Nat.card ι) (d : Faces F) : 3≤(faceVertices F d).card := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have h3 := face_edges_card_three F hF Q hQ hcard d
  obtain ⟨x,hx,y,hy,hxy⟩ := faceVertices_nontrivial F hF Q hQ d
  have h2 : 2≤(faceVertices F d).card := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
  by_contra hn
  have heq : (faceVertices F d).card=2 := by omega
  obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp heq
  have hend (i : ι) (hi : i∈regionEdges F ConnectedComponents.mk d) (t : I) (ht : t=0 ∨ t=1) :
      F i t=a ∨ F i t=b := by
    have hv : F i t∈faceVertices F d := (mem_faceVertices F d _).mpr ⟨⟨i,by rcases ht with rfl|rfl <;> simp⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi (mem_range_self t)⟩
    simpa only [heq,Finset.mem_insert,Finset.mem_singleton] using hv
  have hpair (i : ι) (hi : i∈regionEdges F ConnectedComponents.mk d) : a∈range (F i) ∧ b∈range (F i) := by
    have h₀ := hend i hi 0 (Or.inl rfl)
    have h₁ := hend i hi 1 (Or.inr rfl)
    rcases h₀ with h₀|h₀ <;> rcases h₁ with h₁|h₁
    · exact False.elim ((F i).endpoints_ne (h₀.trans h₁.symm))
    · exact ⟨⟨0,h₀⟩,⟨1,h₁⟩⟩
    · exact ⟨⟨1,h₁⟩,⟨0,h₀⟩⟩
    · exact False.elim ((F i).endpoints_ne (h₀.trans h₁.symm))
  have hs : (regionEdges F ConnectedComponents.mk d).Subsingleton := by
    intro i hi j hj
    by_contra hij
    exact hab ((hF hij).2 ⟨(hpair i hi).1,(hpair j hj).1⟩ ⟨(hpair i hi).2,(hpair j hj).2⟩)
  have hsmall : Nat.card (regionEdges F ConnectedComponents.mk d)≤1 := by
    let _ : Subsingleton (regionEdges F ConnectedComponents.mk d) := hs.coe_sort
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  omega

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
