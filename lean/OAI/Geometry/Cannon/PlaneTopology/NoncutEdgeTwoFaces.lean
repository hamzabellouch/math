import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.TamePairJordanRegions
import OAI.Geometry.Cannon.PlaneTopology.Spans
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
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem noncut_edge_two_faces (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ d₀ d₁ : Faces F,d₀≠d₁ ∧ e∈regionEdges F ConnectedComponents.mk d₀ ∧
      e∈regionEdges F ConnectedComponents.mk d₁ := by
  classical
  let K := ⋃ i,range (F i)
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨b,hb₀,hb₁,hbK,⟨P,hP⟩,hab⟩ := edge_on_tame_cycle F hF Q hQ hK e
  have ha' : range (F e)⊆⋃q∈Q∪P,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hQ e hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_left P hq,hzq⟩
  have hb' : range b⊆⋃q∈Q∪P,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hP hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_right Q hq,hzq⟩
  obtain ⟨R,hR,hdis,hcov⟩ := tame_pair_jordan_regions (F e) b hb₀.symm hb₁.symm hab (Q∪P) ha' hb'
  have hsub (d : Faces F) : face F d⊆R false ∨ face F d⊆R true := by
    apply (component_region_connected Kᶜ d).isPreconnected.subset_or_subset (hR false).1 (hR true).1 hdis
    rw [hcov]
    intro z hz hh
    exact hz.1 (hh.elim (fun h=>mem_iUnion.mpr ⟨e,h⟩) (fun h=>hbK h))
  have hkey (i : Bool) {z : ℂ} (hz : z∈R i) (hzK : z∉K) :
      face F (ConnectedComponents.mk ⟨z,hzK⟩)⊆R i := by
    have hzF : z∈face F (ConnectedComponents.mk ⟨z,hzK⟩) := ⟨hzK,rfl⟩
    rcases hsub (ConnectedComponents.mk ⟨z,hzK⟩) with hh|hh
    · cases i
      · exact hh
      · exact False.elim (disjoint_left.mp hdis (hh hzF) hz)
    · cases i
      · exact False.elim (disjoint_left.mp hdis hz (hh hzF))
      · exact hh
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : (0:I)<t := by change (0:ℝ)<1/2; norm_num
  have ht₁ : t<(1:I) := by change (1/2:ℝ)<1; norm_num
  have hfind (i : Bool) : ∃ d : Faces F,face F d⊆R i ∧ F e t∈closure (face F d) := by
    let B : Set (Faces F) := {d | face F d⊆R i}
    let T := ⋃ d∈B,closure (face F d)
    have hT : IsClosed T := isClosed_iUnion_of_finite fun d=>isClosed_iUnion_of_finite fun _=>isClosed_closure
    have hd : Dense (Kᶜ : Set ℂ) :=
      (complex_finite_segments_compl_dense Q).mono (compl_subset_compl.mpr (iUnion_subset hQ))
    have hinc : R i∩Kᶜ⊆T := by
      intro z hz
      exact mem_iUnion₂.mpr ⟨ConnectedComponents.mk ⟨z,hz.2⟩,hkey i hz.1 hz.2,subset_closure ⟨hz.2,rfl⟩⟩
    have hRT : R i⊆T := by
      intro z hz
      exact closure_minimal hinc hT ((hR i).1.inter_closure ⟨hz,hd z⟩)
    have hx : F e t∈closure (R i) := by
      rw [(hR i).2.2.1]
      exact Or.inr (Or.inl (mem_range_self t))
    obtain ⟨d,hd,hx⟩ := mem_iUnion₂.mp (closure_minimal hRT hT hx)
    exact ⟨d,hd,hx⟩
  obtain ⟨d₀,hd₀,hx₀⟩ := hfind false
  obtain ⟨d₁,hd₁,hx₁⟩ := hfind true
  refine ⟨d₀,d₁,?_,⟨t,ht₀,ht₁,hx₀⟩,⟨t,ht₀,ht₁,hx₁⟩⟩
  intro he
  obtain ⟨z,hz⟩ := face_nonempty F d₀
  exact disjoint_left.mp hdis (hd₀ hz) (hd₁ (he ▸ hz))

theorem noncut_total_face_incidence (F : ι → Arc ℂ) [Fintype (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    (∑ d : Faces F,Nat.card (regionEdges F ConnectedComponents.mk d))=2*Nat.card ι := by
  classical
  let R (i : ι) := {d : Faces F | i∈regionEdges F ConnectedComponents.mk d}
  have hR (i : ι) : 2≤Nat.card (R i) := by
    obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i
    have hn : (R i).Nontrivial := ⟨a,ha,b,hb,hab⟩
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr hn
  let e : (Σ d : Faces F,regionEdges F ConnectedComponents.mk d) ≃ Σ i : ι,R i :=
    { toFun := fun ⟨d,i⟩ => ⟨i.val,⟨d,i.property⟩⟩
      invFun := fun ⟨i,d⟩ => ⟨d.val,⟨i,d.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply Nat.le_antisymm (total_face_incidence_le F hF Q hQ)
  calc
    _=∑ _ : ι,2 := by simp [Nat.card_eq_fintype_card,mul_comm]
    _≤∑ i : ι,Nat.card (R i) := Finset.sum_le_sum (fun i _=>hR i)
    _=Nat.card (Σ i : ι,R i) := (Nat.card_sigma).symm
    _=Nat.card (Σ d : Faces F,regionEdges F ConnectedComponents.mk d) := (Nat.card_congr e).symm
    _=_ := Nat.card_sigma

omit [Nonempty ι] in
theorem triangle_region_edges (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (d : Faces F) (i j k : ι)
    (hcl : closure (face F d)=face F d∪(range (F i)∪range (F j)∪range (F k))) :
    regionEdges F ConnectedComponents.mk d={i,j,k} := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : (0:I)<t := by change (0:ℝ)<1/2; norm_num
  have ht₁ : t<(1:I) := by change (1/2:ℝ)<1; norm_num
  have huniq (a b : ι) (h : F a t∈range (F b)) : a=b := by
    by_contra hab
    obtain ⟨s,hs⟩ := h
    exact ((hF hab).1 t s hs.symm).1.elim ht₀.ne' ht₁.ne
  ext a
  constructor
  · intro ha
    have hx := region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha (mem_range_self t)
    change F a t∈closure (face F d) at hx
    rw [hcl] at hx
    rcases hx with hx|hx
    · exact False.elim (hx.1 (mem_iUnion.mpr ⟨a,mem_range_self t⟩))
    · rcases hx with (hx|hx)|hx
      · exact Or.inl (huniq a i hx)
      · exact Or.inr (Or.inl (huniq a j hx))
      · exact Or.inr (Or.inr (huniq a k hx))
  · rintro (rfl|rfl|rfl) <;> refine ⟨t,ht₀,ht₁,?_⟩ <;>
      change _∈closure (face F d) <;> rw [hcl]
    · exact Or.inr (Or.inl (Or.inl (mem_range_self t)))
    · exact Or.inr (Or.inl (Or.inr (mem_range_self t)))
    · exact Or.inr (Or.inr (mem_range_self t))

omit [Nonempty ι] in
theorem noncut_facial_vertices_edges (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    (faceVertices F d).card=Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let V := faceVertices F d
  let C (q : V) : Set E := {e | q.val∈range (F e.val)}
  let B (e : E) : Set V := {q | q.val∈range (F e.val)}
  have hC (q : V) : Nat.card (C q)=2 := by
    have hq := (mem_faceVertices F d q.val).mp q.property
    have hq' := hq.2
    have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
    change closure (face F d)=face F d∪⋃ e∈E,range (F e) at hcl
    rw [hcl] at hq'
    have hs : q.val∈⋃ e∈E,range (F e) := hq'.resolve_left (fun hh=>hh.1 (vertex_mem_support F hq.1))
    obtain ⟨i,hi,hqi⟩ := mem_iUnion₂.mp hs
    obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF Q hQ hK d hq.1 hi hqi
    let i' : E := ⟨i,hi⟩
    let j' : E := ⟨j,hj⟩
    change (C q).ncard=2
    apply Set.ncard_eq_two.mpr
    refine ⟨i',j',fun he=>hji (congrArg Subtype.val he).symm,?_⟩
    ext k
    constructor
    · intro hk
      rcases face_edge_eq F hF Q hQ hq.1 (hK q.val) d hji.symm hi hj k.property hqi hqj hk with h|h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl|rfl)
      · exact hqi
      · exact hqj
  have hB (e : E) : Nat.card (B e)=2 := by
    have hend (t : I) (ht : t=0 ∨ t=1) : F e.val t∈V := by
      apply (mem_faceVertices F d _).mpr
      refine ⟨⟨e.val,?_⟩,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe e.property (mem_range_self t)⟩
      rcases ht with rfl|rfl <;> simp
    let a : V := ⟨F e.val 0,hend 0 (Or.inl rfl)⟩
    let b : V := ⟨F e.val 1,hend 1 (Or.inr rfl)⟩
    change (B e).ncard=2
    apply Set.ncard_eq_two.mpr
    refine ⟨a,b,fun he=>(F e.val).endpoints_ne (congrArg Subtype.val he),?_⟩
    ext q
    constructor
    · rintro ⟨t,ht⟩
      have hv := (mem_faceVertices F d q.val).mp q.property |>.1
      rcases vertex_parameter F hF e.val (ht.symm ▸ hv) with h|h
      · subst t
        exact Or.inl (Subtype.ext ht.symm)
      · subst t
        exact Or.inr (Subtype.ext ht.symm)
    · rintro (rfl|rfl)
      · exact mem_range_self 0
      · exact mem_range_self 1
  let e : (Σ q : V,C q) ≃ Σ i : E,B i :=
    { toFun := fun ⟨q,i⟩=>⟨i.val,⟨q,i.property⟩⟩
      invFun := fun ⟨i,q⟩=>⟨q.val,⟨i,q.property⟩⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  have hh := Nat.card_congr e
  rw [Nat.card_sigma,Nat.card_sigma] at hh
  simp only [hC,hB,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  simp only [Fintype.card_coe] at hh
  have heq : V.card=Fintype.card E := by omega
  simpa only [V,E,Nat.card_eq_fintype_card] using heq

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
end

end OAI
