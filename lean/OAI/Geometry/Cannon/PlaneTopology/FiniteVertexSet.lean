import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.TameEdgeIncidenceLocal
import OAI.Geometry.Cannon.PlanarGraphs.ClosureRegionInside

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

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma finite_vertex_set (F : ι → Arc ℂ) : {x | Vertex F x}.Finite := by
  have he : {x | Vertex F x}=range (fun i => F i 0)∪range (fun i => F i 1) := by
    ext x
    simp only [mem_ofPred_eq,Vertex,mem_union,mem_range]
    aesop
  rw [he]
  exact (finite_range _).union (finite_range _)

omit [Finite ι] in
lemma interior_not_vertex (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) : ¬Vertex F (F i t) := by
  rintro ⟨j,hj⟩
  by_cases hij : i=j
  · subst j
    rcases hj with h|h
    · exact ht₀.ne' ((F i).injective h).symm
    · exact ht₁.ne ((F i).injective h).symm
  · rcases hj with h|h
    · rcases ((hF hij).1 t 0 h.symm).1 with h|h
      · exact ht₀.ne' h
      · exact ht₁.ne h
    · rcases ((hF hij).1 t 1 h.symm).1 with h|h
      · exact ht₀.ne' h
      · exact ht₁.ne h

theorem tame_face_hits_edge [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region _ π d).Nonempty) :
    ∃ (i : ι) (t : I), 0<t ∧ t<1 ∧ d∈incident _ π (F i t) := by
  let K : Set ℂ := ⋃ j, range (F j)
  let T : Set ℂ := {x | Vertex F x}
  have hTK : T⊆K := by
    rintro x ⟨i,hi⟩
    apply mem_iUnion.mpr
    rcases hi with h|h
    · exact ⟨i,⟨0,h⟩⟩
    · exact ⟨i,⟨1,h⟩⟩
  have hconn : IsPreconnected Tᶜ := by
    apply (Set.Countable.isPathConnected_compl_of_one_lt_rank (E:=ℂ) ?_
      (finite_vertex_set F).countable).isConnected.isPreconnected
    rw [Complex.rank_real_complex]
    norm_num
  have hne : (K\T).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    let t : I := ⟨1/2,by constructor <;> norm_num⟩
    refine ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩,interior_not_vertex F hF i ?_ ?_⟩
    · change (0:ℝ)<1/2
      norm_num
    · change (1/2:ℝ)<1
      norm_num
  obtain ⟨x,hxK,hxT,hxd⟩ := region_boundary_hits
    (show IsClosed K from isClosed_iUnion_of_finite (fun i => (F i).compact_range.isClosed))
    (finite_vertex_set F).isClosed hTK hconn hne hπ d hd
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hxK
  have ht₀ : t≠0 := by
    intro h
    apply hxT
    exact ⟨i,Or.inl (congrArg (F i) h.symm)⟩
  have ht₁ : t≠1 := by
    intro h
    apply hxT
    exact ⟨i,Or.inr (congrArg (F i) h.symm)⟩
  exact ⟨i,t,lt_of_le_of_ne (show (0:I)≤t from t.property.1) ht₀.symm,
    lt_of_le_of_ne (show t≤(1:I) from t.property.2) ht₁,hxd⟩

theorem tame_face_labels_surjection [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hsur : Function.Surjective π) :
    ∃ f : ι × Bool → D, Function.Surjective f := by
  choose labels hlabels using tame_edge_incident_labels F hF Q hQ hπ
  refine ⟨fun p => labels p.1 p.2,?_⟩
  intro d
  obtain ⟨z,hz⟩ := hsur d
  obtain ⟨i,t,ht₀,ht₁,hd⟩ := tame_face_hits_edge F hF hπ d ⟨z.val,z.property,hz⟩
  rw [hlabels i t ht₀ ht₁] at hd
  obtain ⟨b,hb⟩ := hd
  exact ⟨(i,b),hb⟩

theorem tame_face_labels_card [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hsur : Function.Surjective π) : Nat.card D≤2*Nat.card ι := by
  obtain ⟨f,hf⟩ := tame_face_labels_surjection F hF Q hQ hπ hsur
  have h := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_prod,Nat.card_eq_fintype_card,mul_comm] using h
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

end OAI
