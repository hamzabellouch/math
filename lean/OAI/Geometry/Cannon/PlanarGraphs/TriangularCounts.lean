import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Support
import OAI.Geometry.Cannon.PlaneTopology.NoncutEdgeTwoFaces

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
noncomputable section
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem triangular_counts (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (htri : ∀ d : Faces F,∃ i j k : ι,i≠j ∧ j≠k ∧ k≠i ∧
      closure (face F d)=face F d∪(range (F i)∪range (F j)∪range (F k))) :
    (∀ d : Faces F,(faceVertices F d).card=3) ∧
      Nat.card (Faces F)+4=2*(vertices F Finset.univ).card ∧
      Nat.card ι+6=3*(vertices F Finset.univ).card := by
  classical
  let _ : Finite (Faces F) := CannonEmbeddedArc.Arc.faces_finite F hF Q hQ
  let _ := Fintype.ofFinite (Faces F)
  have hthree (d : Faces F) : Nat.card (regionEdges F ConnectedComponents.mk d)=3 := by
    obtain ⟨i,j,k,hij,hjk,hki,hcl⟩ := htri d
    rw [triangle_region_edges F hF Q hQ d i j k hcl,Nat.card_coe_set_eq]
    have hnotMem : i∉({j,k} : Set ι) := by
      rintro (heq|heq)
      · exact hij heq
      · exact hki heq.symm
    rw [Set.ncard_insert_of_notMem hnotMem,Set.ncard_pair hjk]
  have hI := noncut_total_face_incidence F hF Q hQ hK
  simp only [hthree,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card] at hI
  obtain ⟨z,hz⟩ := (complex_finite_segments_compl_dense Q).nonempty
  have hzK : z∉⋃ i,range (F i) := fun h=>hz (iUnion_subset hQ h)
  have hconn : IsPreconnected (support F Finset.univ) := by
    have hh := hK z
    rw [sdiff_singleton_eq_self hzK] at hh
    simpa only [support,Finset.mem_univ,iUnion_true] using hh
  have hEuler := planar_euler F hF Q hQ hconn
  have hfaces : faces F Finset.univ=Nat.card (Faces F) := by
    unfold faces support Faces
    have he : (⋃ i∈(Finset.univ : Finset ι),range (F i))=⋃ i,range (F i) := by simp
    rw [he]
  rw [hfaces,Nat.card_eq_fintype_card] at hEuler
  refine ⟨fun d=>(noncut_facial_vertices_edges F hF Q hQ hK d).trans (hthree d),?_,?_⟩ <;>
    rw [Nat.card_eq_fintype_card] <;> omega
end CannonPlanarEuler

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
end

end OAI
