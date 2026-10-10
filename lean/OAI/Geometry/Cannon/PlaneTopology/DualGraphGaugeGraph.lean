import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.DualGraph
import OAI.Geometry.Cannon.PlanarGraphs.EdgeGraph

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

lemma dualGraph_eq_gaugeGraph (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i)) (E : Set ι) :
    dualGraph F E=CannonGraphGauge.edgeGraph a b hab E := by
  ext x y
  constructor
  · rintro ⟨hxy,i,hi,hx,hy⟩
    refine ⟨i,hi,?_⟩
    rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hx with hx|hx <;>
      rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hy with hy|hy
    · exact (hxy (hx.trans hy.symm)).elim
    · exact Or.inl ⟨hx.symm,hy.symm⟩
    · exact Or.inr ⟨hy.symm,hx.symm⟩
    · exact (hxy (hx.trans hy.symm)).elim
  · rintro ⟨i,hi,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact ⟨hab i,i,hi,ha i,hb i⟩
    · exact ⟨(hab i).symm,i,hi,hb i,ha i⟩

lemma no_single_bad_transition (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (K : ι→D) (v t : Faces F→D) {q : ℂ} (hq : Vertex F q)
    (hlocal : ∀ j,q∈range (F j) → K j*t (a j)=t (b j))
    (i : ι) (hi : q∈range (F i))
    (hother : ∀ j,q∈range (F j) → j≠i → K j*v (a j)=v (b j)) :
    K i*v (a i)=v (b i) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let f (d : Faces F) := (t d)⁻¹*v d
  let w : IncidentEdges F q ⊕ IncidentFaces F q → D :=
    Sum.elim (fun j=>f (a j.val)) (fun d=>f d.val)
  let i' : IncidentEdges F q := ⟨i,hi⟩
  let b' : IncidentFaces F q := ⟨b i,region_edge_in_closure F hF Q hQ
    ConnectedComponents.continuous_coe (hb i) hi⟩
  have good (j : ι) (hj : q∈range (F j)) (hji : j≠i) : f (a j)=f (b j) := by
    simp only [f,←hlocal j hj,←hother j hj hji,mul_inv_rev]
    group
  have step (j : IncidentEdges F q) (d : IncidentFaces F q)
      (hd : j.val∈regionEdges F ConnectedComponents.mk d.val)
      (hne : s(Sum.inl j,Sum.inr d)≠s(Sum.inl i',Sum.inr b')) :
      w (.inl j)=w (.inr d) := by
    change f (a j.val)=f d.val
    rcases edge_face_unique_two F hF Q hQ j.val (hab j.val) (ha j.val) (hb j.val) hd with h|h
    · rw [h]
    · rw [h]
      apply good _ j.property
      intro he
      apply hne
      have hj : j=i' := Subtype.ext he
      have hd : d=b' := Subtype.ext (h.trans (congrArg b he))
      rw [hj,hd]
  have he := CannonGraphGauge.label_equal_of_other_edges (vertexLink F q)
    (vertexLink_isCycles F hF Q hQ hK hq)
    (show (vertexLink F q).Adj (.inl i') (.inr b') from hb i) w (by
      intro x y h hne
      cases x with
      | inl j =>
        cases y with
        | inl k => exact h.elim
        | inr d => exact step j d h hne
      | inr d =>
        cases y with
        | inr c => exact h.elim
        | inl j =>
          apply (step j d h ?_).symm
          intro he
          exact hne (Sym2.eq_swap.trans he))
  change (t (a i))⁻¹*v (a i)=(t (b i))⁻¹*v (b i) at he
  have he' := congrArg (fun z=>t (b i)*z) he
  rw [←hlocal i hi] at he'
  group at he'
  exact he'

theorem planar_local_gauge_integrates (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (K : ι→D)
    (hflat : ∀ q,Vertex F q → ∃ t : Faces F→D,
      ∀ j,q∈range (F j) → K j*t (a j)=t (b j)) :
    ∃ v : Faces F→D,∀ i,K i*v (a i)=v (b i) := by
  classical
  have hconn : (CannonGraphGauge.edgeGraph a b hab univ).Preconnected := by
    rw [←dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact dualGraph_preconnected F hF Q hQ
  obtain ⟨v,hv⟩ := CannonGraphGauge.exists_connected_good a b hab K hconn
  let E : Set ι := (CannonGraphGauge.goodEdges a b K v : Set ι)
  have hd : (dualGraph F E).Preconnected := by
    rw [dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact hv
  have hac := nonseparating_isAcyclic F hF Q hQ Eᶜ
    (complement_preconnected_of_dual F hF Q hQ E hd)
  have hempty : edgeGraph F Eᶜ=⊥ := by
    apply CannonForest.empty_of_no_leaves _ hac
    rintro x y ⟨i,hi,hiy⟩
    by_contra hn
    push Not at hn
    obtain ⟨t,ht⟩ := hflat x.val x.property
    have he : K i*v (a i)=v (b i) := no_single_bad_transition F hF Q hQ hK a b hab ha hb
      K v t x.property ht i hiy.mem_left (by
        intro j hj hji
        by_contra hbad
        obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hj
        let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
        have hAdj : (edgeGraph F Eᶜ).Adj x z' := ⟨j,by simpa [E] using hbad,hjz⟩
        have hzy := congrArg Subtype.val (hn z' hAdj)
        exact hji (spans_edge_unique F hF (hzy ▸ hjz) hiy))
    exact hi (by simpa [E] using he)
  refine ⟨v,fun i=>?_⟩
  by_contra hn
  let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
  let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
  have h : (edgeGraph F Eᶜ).Adj x y := ⟨i,by simpa [E] using hn,Or.inl ⟨rfl,rfl⟩⟩
  rw [hempty] at h
  exact h
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
