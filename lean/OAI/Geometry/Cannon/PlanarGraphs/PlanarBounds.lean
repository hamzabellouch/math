import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.ConnectedPlanarBounds
import OAI.Geometry.Cannon.PlaneTopology.FaceVerticesCardThree

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
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
theorem planar_bounds (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcard : 3≤Nat.card ι) :
    Fintype.card ι+6≤3*(vertices F Finset.univ).card ∧
      Nat.card (Faces F)+4≤2*(vertices F Finset.univ).card := by
  classical
  let _ : Finite (Faces F) := CannonEmbeddedArc.Arc.faces_finite F hF Q hQ
  let _ := Fintype.ofFinite (Faces F)
  obtain ⟨c,A,hc,hA,h₀,h₁,hAS,hU⟩ := global_vertex_stellation F hF Q hQ
  let κ := ι ⊕ (Σ d : Faces F,faceVertices F d)
  let H : κ → Arc ℂ := Sum.elim F A
  have hHS : ∀ k,FiniteSupport (range (H k)) := by
    intro k
    rcases k with i|i
    · exact ⟨Q,hQ i⟩
    · exact hAS i
  obtain ⟨P,hP⟩ := FiniteSupport.iUnion hHS
  have hHP (k : κ) : range (H k)⊆⋃ q∈P,segment ℝ q.1 q.2 :=
    (subset_iUnion (fun k => range (H k)) k).trans hP
  have hsupp : support H Finset.univ=(⋃ i,range (F i))∪⋃ i,range (A i) := by
    simp [support,H,κ,iUnion_sum]
  let i₀ : ι := Classical.choice inferInstance
  have hsingle : range (F i₀)⊆support H Finset.univ := by
    rw [hsupp]
    exact (subset_iUnion (fun i=>range (F i)) i₀).trans subset_union_left
  have hconn : IsPreconnected (support H Finset.univ) := by
    have hh := stellar_old_point_no_cut F hF Q hQ c hc A h₀ h₁ hU
      (mem_iUnion.mpr ⟨i₀,mem_range_self (0:I)⟩)
    rw [←hsupp] at hh
    have hx : ((support H Finset.univ\{F i₀ 0})∩range (F i₀)).Nonempty :=
      ⟨F i₀ 1,⟨hsingle (mem_range_self 1),fun he => (F i₀).endpoints_ne he.symm⟩,mem_range_self 1⟩
    have hu := hh.union' hx (isPreconnected_range (F i₀).continuous)
    have he : (support H Finset.univ\{F i₀ 0})∪range (F i₀)=support H Finset.univ := by
      ext z
      constructor
      · exact fun h => h.elim (fun h=>h.1) (fun h=>hsingle h)
      · intro hz
        by_cases he : z=F i₀ 0
        · exact Or.inr (he ▸ mem_range_self 0)
        · exact Or.inl ⟨hz,he⟩
    rwa [he] at hu
  have hE : Fintype.card κ=Fintype.card ι+∑ d : Faces F,(faceVertices F d).card := by
    simp only [κ,Fintype.card_sum,Fintype.card_sigma,Fintype.card_coe]
  have hI : 3*Fintype.card (Faces F)≤∑ d : Faces F,(faceVertices F d).card := by
    calc
      _=∑ _ : Faces F,3 := by simp [mul_comm]
      _≤_ := Finset.sum_le_sum fun d _ => face_vertices_card_three F hF Q hQ hcard d
  have hV : (vertices H Finset.univ).card≤(vertices F Finset.univ).card+Fintype.card (Faces F) := by
    have hs : vertices H Finset.univ⊆vertices F Finset.univ∪Finset.univ.image c := by
      intro z hz
      obtain ⟨k,_,hk⟩ := (mem_vertices H Finset.univ z).mp hz
      rcases k with i|i
      · exact Finset.mem_union_left _ ((mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hk⟩)
      · rcases hk with hk|hk
        · apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨i.1,Finset.mem_univ _,(h₀ i).symm.trans hk⟩
        · apply Finset.mem_union_left
          have hv := ((mem_faceVertices F i.1 i.2.val).mp i.2.property).1
          obtain ⟨j,hj⟩ := hv
          exact (mem_vertices F Finset.univ z).mpr ⟨j,Finset.mem_univ _,by
            change A i 1=z at hk
            rw [h₁] at hk
            exact hj.imp (fun h=>h.trans hk) (fun h=>h.trans hk)⟩
    exact (Finset.card_le_card hs).trans ((Finset.card_union_le ..).trans
      (Nat.add_le_add_left ((Finset.card_image_le).trans_eq (Finset.card_univ)) _))
  have hH3 : 3≤Nat.card κ := by rw [Nat.card_eq_fintype_card,hE]; rw [Nat.card_eq_fintype_card] at hcard; omega
  have hB := (connected_planar_bounds H hA P hHP hconn hH3).1
  have hEB : Fintype.card ι+6≤3*(vertices F Finset.univ).card := by omega
  refine ⟨hEB,?_⟩
  have h3 : 3*Nat.card (Faces F)≤2*Nat.card ι := by
    calc
      _=∑ _ : Faces F,3 := by simp [Nat.card_eq_fintype_card,mul_comm]
      _≤∑ d : Faces F,Nat.card (regionEdges F ConnectedComponents.mk d) :=
        Finset.sum_le_sum (fun d _ => face_edges_card_three F hF Q hQ hcard d)
      _≤_ := total_face_incidence_le F hF Q hQ
  simp only [Nat.card_eq_fintype_card] at h3 ⊢
  omega
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

end OAI
