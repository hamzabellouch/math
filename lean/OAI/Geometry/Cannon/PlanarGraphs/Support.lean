import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.RegionEdges
import OAI.Geometry.Cannon.PlaneTopology.VertexLines
import OAI.Geometry.Cannon.PlaneTopology.OtherComponentDeleteArc

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
namespace CannonPlanarEuler
open Set Topology unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {ι : Type*} [DecidableEq ι]
def support (F : ι → Arc ℂ) (S : Finset ι) : Set ℂ := ⋃ i∈S,range (F i)
def vertices (F : ι → Arc ℂ) (S : Finset ι) : Finset ℂ := by
  classical
  exact S.biUnion fun i => {F i 0,F i 1}
def faces (F : ι → Arc ℂ) (S : Finset ι) : ℕ :=
  Nat.card (ConnectedComponents ((support F S)ᶜ : Set ℂ))
lemma support_insert (F : ι → Arc ℂ) (S : Finset ι) (i : ι) :
    support F (insert i S)=support F S∪range (F i) := by
  simp only [support,Finset.mem_insert,iUnion_iUnion_eq_or_left,union_comm]
lemma vertices_insert (F : ι → Arc ℂ) (S : Finset ι) (i : ι) :
    vertices F (insert i S)=insert (F i 0) (insert (F i 1) (vertices F S)) := by
  classical
  ext x
  simp only [vertices,Finset.biUnion_insert,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto
omit [DecidableEq ι] in
lemma support_closed (F : ι → Arc ℂ) (S : Finset ι) : IsClosed (support F S) :=
  isClosed_biUnion_finset fun i _ => (F i).compact_range.isClosed
omit [DecidableEq ι] in
lemma mem_vertices (F : ι → Arc ℂ) (S : Finset ι) (x : ℂ) :
    x∈vertices F S ↔ ∃ i∈S,F i 0=x ∨ F i 1=x := by
  classical
  simp [vertices,eq_comm]
omit [DecidableEq ι] in
lemma vertices_subset (F : ι → Arc ℂ) (S : Finset ι) : (vertices F S:Set ℂ)⊆support F S := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := (mem_vertices F S x).mp hx
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)⟩⟩
omit [DecidableEq ι] in
lemma support_subtype (F : ι → Arc ℂ) (S : Finset ι) :
    support F S=⋃i:S,range (F i.val) := by ext x; simp [support]
omit [DecidableEq ι] in
lemma support_tame (F : ι → Arc ℂ) (S : Finset ι) (Q : Finset (ℂ × ℂ))
    (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) :
    ∃ P : Finset (ℂ × ℂ),support F S=⋃p∈P,segment ℝ p.1 p.2 := by
  rw [support_subtype]
  exact finite_graph_exact_segments (fun i:S => F i.val) Q (fun i => hQ i.val)
omit [DecidableEq ι] in
lemma faces_finite (F : ι → Arc ℂ) (S : Finset ι) (hS : S.Nonempty)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2) :
    Finite (ConnectedComponents ((support F S)ᶜ : Set ℂ)) := by
  let _ : Nonempty S := hS.to_subtype
  rw [support_subtype]
  exact CannonEmbeddedArc.Arc.faces_finite (fun i:S => F i.val)
    (fun _ _ h => hF (fun he => h (Subtype.ext he))) Q (fun i => hQ i.val)
omit [DecidableEq ι] in
lemma edge_interior_avoids (F : ι → Arc ℂ) (S : Finset ι)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {i : ι} (hi : i∉S) :
    F i '' Ioo (0:I) 1⊆(support F S)ᶜ := by
  rintro x ⟨t,ht,rfl⟩ hx
  simp only [support,mem_iUnion] at hx
  obtain ⟨j,hj,s,hs⟩ := hx
  have hij : i≠j := fun h => hi (h ▸ hj)
  rcases (hF hij).1 t s hs.symm |>.1 with he|he
  · exact ht.1.ne' he
  · exact ht.2.ne he
omit [DecidableEq ι] in
lemma edge_end_mem_support (F : ι → Arc ℂ) (S : Finset ι)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {i : ι} (hi : i∉S) (t : I) :
    F i t∈support F S ↔ F i t∈vertices F S := by
  constructor
  · intro h
    simp only [support,mem_iUnion] at h
    obtain ⟨j,hj,s,hs⟩ := h
    refine (mem_vertices F S (F i t)).mpr ⟨j,hj,?_⟩
    rcases (hF (show i≠j from fun h => hi (h ▸ hj))).1 t s hs.symm |>.2 with he|he
    · exact Or.inl (he ▸ hs)
    · exact Or.inr (he ▸ hs)
  · exact fun h => vertices_subset F S h

omit [DecidableEq ι] in
lemma edge_face (F : ι → Arc ℂ) (S : Finset ι)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {i : ι} (hi : i∉S) :
    ∃ d : ConnectedComponents ((support F S)ᶜ : Set ℂ),
      F i '' Ioo (0:I) 1⊆region _ ConnectedComponents.mk d ∧
      ∀ t:I, F i t∉support F S → F i t∈region _ ConnectedComponents.mk d := by
  let _ : LocallyConnectedSpace ((support F S)ᶜ : Set ℂ) :=
    (support_closed F S).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((support F S)ᶜ : Set ℂ)) := inferInstance
  have hc : IsConnected (F i '' Ioo (0:I) 1) :=
    (isConnected_Ioo (show (0:I)<1 from zero_lt_one)).image _ (F i).continuous.continuousOn
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe hc (edge_interior_avoids F S hF hi)
  have hcl : range (F i)⊆closure (region _ ConnectedComponents.mk d) :=
    range_in_closed_of_interior (F i) isClosed_closure (fun t ht₀ ht₁ => subset_closure (hd ⟨t,⟨ht₀,ht₁⟩,rfl⟩))
  refine ⟨d,hd,fun t ht => ?_⟩
  exact closure_region_inside (support_closed F S).isOpen_compl ConnectedComponents.continuous_coe
    (hcl (mem_range_self t)) ht

lemma single_arc_faces (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (hQ : range a⊆⋃q∈Q,segment ℝ q.1 q.2) :
    Nat.card (ConnectedComponents ((range a)ᶜ : Set ℂ))=1 := by
  have hconn : IsPreconnected ({a 1}ᶜ : Set ℂ) := by
    convert CannonPlanarNeighborhood.open_preconnected_remove_point isOpen_univ isPreconnected_univ (a 1) using 1
    ext x
    simp only [mem_compl_iff,mem_singleton_iff,mem_sdiff,mem_univ,true_and]
  have ha₀ : a 0∈({a 1}ᶜ : Set ℂ) := fun h => zero_ne_one (a.injective h)
  have hUa : a '' Ioo (0:I) 1⊆({a 1}ᶜ : Set ℂ) := by
    rintro x ⟨t,ht,rfl⟩ h
    exact ht.2.ne (a.injective h)
  have hc := tame_slit_connected a Q hQ isClosed_singleton.isOpen_compl hconn ha₀ hUa (by simp)
  have heq : ({a 1}ᶜ : Set ℂ)\range a=(range a)ᶜ := by
    ext z
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨fun he => h (he ▸ mem_range_self 1),h⟩
  rw [heq] at hc
  exact connected_components_card_one hc

lemma attached_edge_euler (F : ι → Arc ℂ) (S : Finset ι) (hS : S.Nonempty)
    (hconn : IsPreconnected (support F S))
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    {i : ι} (hi : i∉S) (hattach : (support F S∩range (F i)).Nonempty) :
    faces F (insert i S)+(vertices F (insert i S)).card=
      faces F S+(vertices F S).card+1 := by
  classical
  let _ := faces_finite F S hS hF Q hQ
  obtain ⟨d,hd,hdend⟩ := edge_face F S hF hi
  have hdist : F i 0≠F i 1 := fun h => zero_ne_one ((F i).injective h)
  have hatt : F i 0∈support F S ∨ F i 1∈support F S := by
    obtain ⟨x,hx,t,rfl⟩ := hattach
    by_cases ht₀ : t=0
    · exact Or.inl (ht₀ ▸ hx)
    by_cases ht₁ : t=1
    · exact Or.inr (ht₁ ▸ hx)
    exact (edge_interior_avoids F S hF hi ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),
      lt_of_le_of_ne (le_one t) ht₁⟩,rfl⟩ hx).elim
  by_cases h₀ : F i 0∈support F S
  · have hv₀ := (edge_end_mem_support F S hF hi 0).mp h₀
    by_cases h₁ : F i 1∈support F S
    · have hv₁ := (edge_end_mem_support F S hF hi 1).mp h₁
      obtain ⟨P,hP⟩ := support_tame F S Q hQ
      have hf : faces F (insert i S)=faces F S+1 := by
        unfold faces
        rw [support_insert]
        have aux : ∀ d : ConnectedComponents ((support F S)ᶜ : Set ℂ),
            F i '' Ioo (0:I) 1⊆region _ ConnectedComponents.mk d →
            F i 0∈support F S → F i 1∈support F S →
            Nat.card (ConnectedComponents ((support F S∪range (F i))ᶜ : Set ℂ))=
              Nat.card (ConnectedComponents ((support F S)ᶜ : Set ℂ))+1 := by
          rw [hP]
          let _ : Finite (ConnectedComponents ((⋃p∈P,segment ℝ p.1 p.2)ᶜ : Set ℂ)) := by
            rw [←hP]
            exact faces_finite F S hS hF Q hQ
          intro e he he₀ he₁
          exact crosscut_face_count P Q (hP ▸ hconn) (F i) (hQ i) e he₀ he₁ he
        exact aux d hd h₀ h₁
      rw [hf,vertices_insert,Finset.insert_eq_of_mem hv₁,Finset.insert_eq_of_mem hv₀]
      omega
    · have hv₁ : F i 1∉vertices F S := fun h => h₁ (vertices_subset F S h)
      have hf : faces F (insert i S)=faces F S := by
        unfold faces
        rw [support_insert,←reverse_range (F i)]
        apply leaf_face_count (support F S) (support_closed F S) (F i).reverse Q
          (by simpa only [reverse_range] using hQ i) d
        · simpa only [reverse_zero] using hdend 1 h₁
        · simpa only [reverse_one] using h₀
        · rintro x ⟨t,ht,rfl⟩
          apply hd
          refine ⟨unitInterval.symm t,⟨?_,?_⟩,rfl⟩
          · change (0:ℝ)<1-(t:ℝ)
            have hh : (t:ℝ)<1 := ht.2
            linarith
          · change 1-(t:ℝ)<(1:ℝ)
            have hh : (0:ℝ)<t := ht.1
            linarith
      rw [hf,vertices_insert,Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hv₀),Finset.card_insert_of_notMem hv₁]
      omega
  · have h₁ := hatt.resolve_left h₀
    have hv₀ : F i 0∉vertices F S := fun h => h₀ (vertices_subset F S h)
    have hv₁ := (edge_end_mem_support F S hF hi 1).mp h₁
    have hf : faces F (insert i S)=faces F S := by
      unfold faces
      rw [support_insert]
      exact leaf_face_count _ (support_closed F S) (F i) Q (hQ i) d (hdend 0 h₀) h₁ hd
    rw [hf,vertices_insert,Finset.insert_eq_of_mem hv₁,Finset.card_insert_of_notMem hv₀]
    omega
omit [DecidableEq ι] in
lemma mem_support (F : ι → Arc ℂ) (S : Finset ι) (x : ℂ) :
    x∈support F S ↔ ∃ i∈S, x∈range (F i) := by simp only [support,mem_iUnion,exists_prop]
omit [DecidableEq ι] in
lemma support_mono (F : ι → Arc ℂ) {S T : Finset ι} (h : S⊆T) : support F S⊆support F T := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := (mem_support F S x).mp hx
  exact (mem_support F T x).mpr ⟨i,h hi,hx⟩
omit [DecidableEq ι] in
lemma support_nonempty (F : ι → Arc ℂ) (S : Finset ι) (hS : S.Nonempty) : (support F S).Nonempty := by
  obtain ⟨i,hi⟩ := hS
  exact ⟨F i 0,(mem_support ..).mpr ⟨i,hi,mem_range_self 0⟩⟩

lemma exists_attached_edge [Fintype ι] (F : ι → Arc ℂ) (S : Finset ι)
    (hconn : IsPreconnected (support F Finset.univ)) (hS : S.Nonempty) (hSne : S≠Finset.univ) :
    ∃ i∉S, (support F S∩range (F i)).Nonempty := by
  classical
  have hT : (Finset.univ\S).Nonempty := Finset.sdiff_nonempty.mpr (by simpa only [Finset.univ_subset_iff] using hSne)
  have hcover : support F Finset.univ⊆support F S∪support F (Finset.univ\S) := by
    intro x hx
    obtain ⟨i,_,hi⟩ := (mem_support F _ x).mp hx
    by_cases h : i∈S
    · exact Or.inl ((mem_support F S x).mpr ⟨i,h,hi⟩)
    · exact Or.inr ((mem_support F _ x).mpr ⟨i,by simp [h],hi⟩)
  obtain ⟨u,hu⟩ := support_nonempty F S hS
  obtain ⟨v,hv⟩ := support_nonempty F (Finset.univ\S) hT
  obtain ⟨x,_,hxS,hxT⟩ := isPreconnected_closed_iff.mp hconn
    (support F S) (support F (Finset.univ\S)) (support_closed F S) (support_closed F _)
    hcover ⟨u,support_mono F (Finset.subset_univ S) hu,hu⟩
      ⟨v,support_mono F (Finset.subset_univ _) hv,hv⟩
  obtain ⟨i,hi,hix⟩ := (mem_support F _ x).mp hxT
  exact ⟨i,(Finset.mem_sdiff.mp hi).2,x,hxS,hix⟩

theorem planar_euler [Fintype ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hconn : IsPreconnected (support F Finset.univ)) :
    faces F Finset.univ+(vertices F Finset.univ).card=Fintype.card ι+2 := by
  classical
  let good : Finset ι → Prop := fun S => S.Nonempty ∧ IsPreconnected (support F S) ∧
    faces F S+(vertices F S).card=S.card+2
  let A : Finset (Finset ι) := Finset.univ.powerset.filter good
  have hA (S : Finset ι) : S∈A ↔ good S := by simp [A]
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hsupp : support F {i}=range (F i) := by
    simp only [support,Finset.mem_singleton,iUnion_iUnion_eq_left]
  have hv : (vertices F {i}).card=2 := by
    have hn : F i 0≠F i 1 := fun h => zero_ne_one ((F i).injective h)
    simp [vertices,hn]
  have hf : faces F {i}=1 := by
    unfold faces
    rw [hsupp]
    exact single_arc_faces (F i) Q (hQ i)
  have hg : good {i} := ⟨Finset.singleton_nonempty _,hsupp ▸ isPreconnected_range (F i).continuous,by simp [hf,hv]⟩
  obtain ⟨S,hSA,hmax⟩ := A.exists_max_image Finset.card ⟨{i},(hA {i}).mpr hg⟩
  obtain ⟨hSne,hSC,hSE⟩ := (hA S).mp hSA
  have hSuniv : S=Finset.univ := by
    by_contra hn
    obtain ⟨j,hj,hjS⟩ := exists_attached_edge F S hconn hSne hn
    have hnew : good (insert j S) := by
      refine ⟨Finset.insert_nonempty ..,?_,?_⟩
      · rw [support_insert]
        exact hSC.union' hjS (isPreconnected_range (F j).continuous)
      · rw [attached_edge_euler F S hSne hSC hF Q hQ hj hjS,hSE,Finset.card_insert_of_notMem hj]
    have hm := hmax (insert j S) ((hA _).mpr hnew)
    rw [Finset.card_insert_of_notMem hj] at hm
    omega
  subst S
  simpa only [Finset.card_univ] using hSE
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

end OAI
