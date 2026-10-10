import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.RegionEdges
import OAI.Geometry.Cannon.PlaneTopology.VertexLines

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
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal

theorem free_arc_delete_connected (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (h₀ : a 0∈U) (hI : a '' Ioo (0:I) 1⊆U) : IsConnected (U\range a) := by
  have hc := CannonPlanarNeighborhood.open_preconnected_remove_point hU hconn (a 1)
  have h := tame_slit_connected a Q ha (hU.sdiff isClosed_singleton) hc
    (show a 0∈U\{a 1} from ⟨h₀,a.endpoints_ne⟩)
    (show a '' Ioo (0:I) 1⊆U\{a 1} from by
      rintro x ⟨t,ht,rfl⟩
      exact ⟨hI ⟨t,ht,rfl⟩,fun he => ht.2.ne (a.injective he)⟩)
    (fun h => h.2 rfl)
  have he : (U\{a 1})\range a=U\range a := by
    ext x
    simp only [mem_sdiff,mem_singleton_iff]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,fun hx => h.2 ⟨1,hx.symm⟩⟩,h.2⟩⟩
  rwa [he] at h

lemma compatible_pair_complement (a b : Arc ℂ) (hab : Compatible a b)
    (Q : Finset (ℂ × ℂ)) (ha : range a⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hb : range b⊆⋃q∈Q,segment ℝ q.1 q.2) : IsConnected ((range a∪range b)ᶜ : Set ℂ) := by
  have hac : IsConnected ((range a)ᶜ : Set ℂ) := by
    simpa only [sdiff_eq_compl_inter,inter_univ] using free_arc_delete_connected a Q ha isOpen_univ isPreconnected_univ (mem_univ _) (subset_univ _)
  have hI : b '' Ioo (0:I) 1⊆(range a)ᶜ := by
    rintro x ⟨t,ht,rfl⟩ ⟨s,hs⟩
    exact ((hab.1 s t hs).2).elim (fun h => ht.1.ne' h) (fun h => ht.2.ne h)
  have hf : b 0∉range a ∨ b 1∉range a := by
    by_contra hn
    push Not at hn
    exact b.endpoints_ne (hab.2 ⟨hn.1,mem_range_self 0⟩ ⟨hn.2,mem_range_self 1⟩)
  rcases hf with h₀|h₁
  · have h := free_arc_delete_connected b Q hb a.compact_range.isClosed.isOpen_compl hac.isPreconnected h₀ hI
    simpa only [compl_union,sdiff_eq_compl_inter,inter_comm] using h
  · have hI' : b.reverse '' Ioo (0:I) 1⊆(range a)ᶜ := by
      rintro x ⟨t,ht,rfl⟩
      apply hI
      refine ⟨unitInterval.symm t,⟨?_,?_⟩,rfl⟩
      · simpa only [unitInterval.symm_one] using (unitInterval.symm_lt_symm.mpr ht.2)
      · simpa only [unitInterval.symm_zero] using (unitInterval.symm_lt_symm.mpr ht.1)
    have h := free_arc_delete_connected b.reverse Q (by simpa only [reverse_range] using hb)
      a.compact_range.isClosed.isOpen_compl hac.isPreconnected (by rw [reverse_zero]; exact h₁) hI'
    simpa only [reverse_range,compl_union,sdiff_eq_compl_inter,inter_comm] using h

variable {ι : Type*} [Finite ι]
omit [Finite ι] in
lemma at_most_two_edges_complement (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (S : Finset ι) (hS : S.card≤2) : IsPreconnected ((⋃i∈S,range (F i))ᶜ : Set ℂ) := by
  classical
  rcases (show S.card=0 ∨ S.card=1 ∨ S.card=2 by omega) with h|h|h
  · have he := Finset.card_eq_zero.mp h
    subst S
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,compl_empty] using
      (isPreconnected_univ : IsPreconnected (univ : Set ℂ))
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
    simpa only [Finset.mem_singleton,iUnion_iUnion_eq_left,sdiff_eq_compl_inter,inter_univ] using
      (free_arc_delete_connected (F i) Q (hQ i) isOpen_univ isPreconnected_univ
        (mem_univ _) (subset_univ _)).isPreconnected
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp h
    simpa only [Finset.mem_insert,Finset.mem_singleton,iUnion_iUnion_eq_or_left,iUnion_iUnion_eq_left] using
      (compatible_pair_complement (F i) (F j) (hF hij) Q (hQ i) (hQ j)).isPreconnected

theorem face_edges_card_three (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcard : 3≤Nat.card ι) (d : Faces F) : 3≤Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let _ := Fintype.ofFinite ι
  let K := ⋃ i,range (F i)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let S : Finset ι := (regionEdges F ConnectedComponents.mk d).toFinite.toFinset
  have hS (i : ι) : i∈S ↔ i∈regionEdges F ConnectedComponents.mk d := by simp [S]
  have hSc : S.card=Nat.card (regionEdges F ConnectedComponents.mk d) := by
    rw [Nat.card_eq_fintype_card]
    exact Set.Finite.card_toFinset _
  by_contra hn
  have hsmall : S.card≤2 := by omega
  have hnot : ∃ i,i∉S := by
    by_contra hh
    push Not at hh
    have hall : S=Finset.univ := Finset.eq_univ_of_forall hh
    rw [hall,Finset.card_univ] at hsmall
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  obtain ⟨i,hi⟩ := hnot
  let T := ⋃ j∈S,range (F j)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => (F j).compact_range.isClosed
  have hTK : T⊆K := by rintro x hx; obtain ⟨j,_,hx⟩ := mem_iUnion₂.mp hx; exact mem_iUnion.mpr ⟨j,hx⟩
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht : t≠0 ∧ t≠1 := by constructor <;> intro h <;> have he := congrArg Subtype.val h <;> norm_num [t] at he
  have hne : (K\T).Nonempty := by
    refine ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩,?_⟩
    intro hh
    obtain ⟨j,hj,u,hu⟩ := mem_iUnion₂.mp hh
    have hij : i≠j := fun h => hi (h ▸ hj)
    exact ((hF hij).1 t u hu.symm).1.elim ht.1 ht.2
  obtain ⟨x,hxK,hxT,hx⟩ := region_boundary_hits hK hT hTK
    (at_most_two_edges_complement F hF Q hQ S hsmall) hne
    ConnectedComponents.continuous_coe d (face_nonempty F d)
  have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
  change x∈closure (region (⋃ j,range (F j))ᶜ ConnectedComponents.mk d) at hx
  rw [hcl] at hx
  rcases hx with hx|hx
  · exact hx.1 hxK
  · apply hxT
    obtain ⟨j,hj,hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨j,(hS j).mpr hj,hx⟩

lemma face_finite [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) : Finite (Faces F) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨f,hf⟩ := tame_face_labels_surjection F hF Q hQ
    ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  exact Finite.of_surjective f hf

theorem total_face_incidence_le (F : ι → Arc ℂ) [Fintype ι] [Fintype (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) :
    (∑ d : Faces F,Nat.card (regionEdges F ConnectedComponents.mk d))≤2*Nat.card ι := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let R (i : ι) := {d : Faces F | i∈regionEdges F ConnectedComponents.mk d}
  have hR (i : ι) : Nat.card (R i)≤2 := by
    obtain ⟨labels,hl⟩ := tame_edge_incident_labels F hF Q hQ ConnectedComponents.continuous_coe i
    have hs : R i⊆range labels := by
      rintro d ⟨t,ht₀,ht₁,hd⟩
      rw [hl t ht₀ ht₁] at hd
      exact hd
    have h1 := Nat.card_mono (toFinite (range labels)) hs
    have h2 : Nat.card (range labels)≤Nat.card Bool :=
      Nat.card_le_card_of_surjective (fun b => (⟨labels b,mem_range_self b⟩ : range labels)) (by
        rintro ⟨d,⟨b,rfl⟩⟩; exact ⟨b,rfl⟩)
    exact h1.trans (by simpa using h2)
  let e : (Σ d : Faces F,regionEdges F ConnectedComponents.mk d) ≃ Σ i : ι,R i :=
    { toFun := fun ⟨d,i⟩ => ⟨i.val,⟨d,i.property⟩⟩
      invFun := fun ⟨i,d⟩ => ⟨d.val,⟨i,d.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _=Nat.card (Σ d : Faces F,regionEdges F ConnectedComponents.mk d) := (Nat.card_sigma).symm
    _=Nat.card (Σ i : ι,R i) := Nat.card_congr e
    _=∑ i : ι,Nat.card (R i) := Nat.card_sigma
    _≤∑ _ : ι,2 := Finset.sum_le_sum (fun i _ => hR i)
    _=2*Nat.card ι := by simp [Nat.card_eq_fintype_card,mul_comm]

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

end OAI
