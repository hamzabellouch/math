import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.DualGraphGaugeGraph
import OAI.Geometry.Cannon.PlanarGraphs.EdgesConfinedCore

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D Z : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

lemma no_single_face_discordance (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (f : Faces F→Z) {q : ℂ} (hq : Vertex F q)
    (i : ι) (hi : q∈range (F i))
    (hother : ∀ j,q∈range (F j) → j≠i → f (a j)=f (b j)) : f (a i)=f (b i) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let w : IncidentEdges F q ⊕ IncidentFaces F q → Z :=
    Sum.elim (fun j=>f (a j.val)) (fun d=>f d.val)
  let i' : IncidentEdges F q := ⟨i,hi⟩
  let b' : IncidentFaces F q := ⟨b i,region_edge_in_closure F hF Q hQ
    ConnectedComponents.continuous_coe (hb i) hi⟩
  have step (j : IncidentEdges F q) (d : IncidentFaces F q)
      (hd : j.val∈regionEdges F ConnectedComponents.mk d.val)
      (hne : s(Sum.inl j,Sum.inr d)≠s(Sum.inl i',Sum.inr b')) :
      w (.inl j)=w (.inr d) := by
    change f (a j.val)=f d.val
    rcases edge_face_unique_two F hF Q hQ j.val (hab j.val) (ha j.val) (hb j.val) hd with h|h
    · rw [h]
    · rw [h]
      apply hother _ j.property
      intro he
      apply hne
      have hj : j=i' := Subtype.ext he
      have hd : d=b' := Subtype.ext (h.trans (congrArg b he))
      rw [hj,hd]
  exact CannonGraphGauge.label_equal_of_other_edges (vertexLink F q)
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

theorem dual_preconnected_delete_forest (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (T : Set ι) (hT : (edgeGraph F T).IsAcyclic) :
    (dualGraph F Tᶜ).Preconnected := by
  classical
  let H := dualGraph F Tᶜ
  let f := H.connectedComponentMk
  let B : Set ι := {i | f (a i)≠f (b i)}
  have hBT : B⊆T := by
    intro i hi
    by_contra hn
    exact hi (SimpleGraph.ConnectedComponent.sound
      (show H.Adj (a i) (b i) from ⟨hab i,i,hn,ha i,hb i⟩).reachable)
  have hBG : edgeGraph F B≤edgeGraph F T := by
    rintro x y ⟨i,hi,h⟩; exact ⟨i,hBT hi,h⟩
  have hempty : edgeGraph F B=⊥ := by
    apply CannonForest.empty_of_no_leaves _ (hT.anti hBG)
    rintro x y ⟨i,hi,hiy⟩
    by_contra hn
    push Not at hn
    apply hi
    exact no_single_face_discordance F hF Q hQ hK a b hab ha hb f x.property i
      hiy.mem_left (by
        intro j hj hji
        by_contra hbad
        obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hj
        let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
        have hAdj : (edgeGraph F B).Adj x z' := ⟨j,hbad,hjz⟩
        have hzy := congrArg Subtype.val (hn z' hAdj)
        exact hji (spans_edge_unique F hF (hzy ▸ hjz) hiy))
  have he (i:ι) : f (a i)=f (b i) := by
    by_contra hn
    let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
    let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
    have h : (edgeGraph F B).Adj x y := ⟨i,hn,Or.inl ⟨rfl,rfl⟩⟩
    rw [hempty] at h
    exact h
  intro x y
  have hc : (CannonGraphGauge.edgeGraph a b hab univ).Preconnected := by
    rw [←dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact dualGraph_preconnected F hF Q hQ
  obtain ⟨p⟩ := hc x y
  apply SimpleGraph.ConnectedComponent.exact
  induction p with
  | nil => rfl
  | @cons x y z h p ih =>
    obtain ⟨i,-,h|h⟩ := h
    · exact (h.1 ▸ h.2 ▸ he i).trans ih
    · exact (h.2 ▸ h.1 ▸ (he i).symm).trans ih

theorem planar_disk_gauge_integrates (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (T : Set ι) (hT : (edgeGraph F T).IsAcyclic)
    (S : Set (GraphVertices F)) (hS : ((edgeGraph F T).induce S).Preconnected)
    (hTS : ∀ x y,(edgeGraph F T).Adj x y → x∈S ∧ y∈S)
    (K : ι→D)
    (hflat : ∀ q:GraphVertices F,q∉S → ∃ t : Faces F→D,
      ∀ j,q.val∈range (F j) → K j*t (a j)=t (b j)) :
    ∃ v : Faces F→D,∀ i,
      ((⟨F i 0,⟨i,Or.inl rfl⟩⟩:GraphVertices F)∉S ∨
       (⟨F i 1,⟨i,Or.inr rfl⟩⟩:GraphVertices F)∉S) → K i*v (a i)=v (b i) := by
  classical
  have hconn : (CannonGraphGauge.edgeGraph a b hab Tᶜ).Preconnected := by
    rw [←dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact dual_preconnected_delete_forest F hF Q hQ hK a b hab ha hb T hT
  obtain ⟨v,hv⟩ := CannonGraphGauge.exists_connected_good_restrict a b hab K Tᶜ hconn
  let E : Set ι := Tᶜ∩(CannonGraphGauge.goodEdges a b K v : Set ι)
  have hd : (dualGraph F E).Preconnected := by
    rw [dualGraph_eq_gaugeGraph F hF Q hQ a b hab ha hb]
    exact hv
  have hac := nonseparating_isAcyclic F hF Q hQ Eᶜ
    (complement_preconnected_of_dual F hF Q hQ E hd)
  have hTB : edgeGraph F T≤edgeGraph F Eᶜ := by
    rintro x y ⟨i,hi,h⟩
    exact ⟨i,fun he=>he.1 hi,h⟩
  have hconnS : ((edgeGraph F Eᶜ).induce S).Preconnected := by
    apply hS.mono
    exact fun _ _ h=>hTB h
  have hconfine := CannonForest.edges_confined_to_core (edgeGraph F Eᶜ) hac S hconnS (by
    rintro x hx y ⟨i,hi,hiy⟩
    by_contra hn
    push Not at hn
    obtain ⟨t,ht⟩ := hflat x hx
    have he : K i*v (a i)=v (b i) := no_single_bad_transition F hF Q hQ hK a b hab ha hb
      K v t x.property ht i hiy.mem_left (by
        intro j hj hji
        by_contra hbad
        obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hj
        let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
        have hjB : j∈Eᶜ := fun h=>hbad ((CannonGraphGauge.mem_goodEdges ..).mp h.2)
        have hAdj : (edgeGraph F Eᶜ).Adj x z' := ⟨j,hjB,hjz⟩
        have hzy := congrArg Subtype.val (hn z' hAdj)
        exact hji (spans_edge_unique F hF (hzy ▸ hjz) hiy))
    have hinT : i∉T := by
      intro hiT
      have hAdj : (edgeGraph F T).Adj x y := ⟨i,hiT,hiy⟩
      exact hx (hTS x y hAdj).1
    exact hi ⟨hinT,(CannonGraphGauge.mem_goodEdges ..).mpr he⟩)
  refine ⟨v,fun i hi=>?_⟩
  by_contra hn
  let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
  let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
  have hB : i∈Eᶜ := fun h=>hn ((CannonGraphGauge.mem_goodEdges ..).mp h.2)
  have h := hconfine x y ⟨i,hB,Or.inl ⟨rfl,rfl⟩⟩
  exact hi.elim (fun hn=>hn h.1) (fun hn=>hn h.2)
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

lemma Spans.endpoints_eq {a:Arc ℂ} {x y u v:ℂ} (h:Spans a x y) (h':Spans a u v) :
    (u=x ∧ v=y) ∨ (u=y ∧ v=x) := by
  rcases h with ⟨hx,hy⟩|⟨hx,hy⟩ <;> rcases h' with ⟨hu,hv⟩|⟨hu,hv⟩
  · exact Or.inl ⟨hu.symm.trans hx,hv.symm.trans hy⟩
  · exact Or.inr ⟨hu.symm.trans hy,hv.symm.trans hx⟩
  · exact Or.inr ⟨hu.symm.trans hy,hv.symm.trans hx⟩
  · exact Or.inl ⟨hu.symm.trans hx,hv.symm.trans hy⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem triangular_face_scaffold [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (out:Faces F) (hthree:(faceVertices F out).card=3) :
    let S : Set (GraphVertices F) := {x | x.val∈faceVertices F out}
    ∃ T:Set ι,(edgeGraph F T).IsAcyclic ∧ ((edgeGraph F T).induce S).Preconnected ∧
      (∀ x y,(edgeGraph F T).Adj x y → x∈S ∧ y∈S) ∧
      ∀ i,F i 0∈faceVertices F out → F i 1∈faceVertices F out →
        i∈regionEdges F ConnectedComponents.mk out := by
  classical
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let S : Set (GraphVertices F) := {x | x.val∈faceVertices F out}
  dsimp only
  have hE : (regionEdges F ConnectedComponents.mk out).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have hn := noncut_facial_vertices_edges F hF Q hQ hK out
    rw [hthree] at hn
    change Nat.card (regionEdges F ConnectedComponents.mk out)≠0
    omega
  obtain ⟨i,hi⟩ := hE
  let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
  let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
  have hixy : Spans (F i) x.val y.val := Or.inl ⟨rfl,rfl⟩
  obtain ⟨j,hji,hj,hxj⟩ := noncut_face_second_edge F hF Q hQ hK out x.property hi hixy.mem_left
  obtain ⟨z₀,hjxz⟩ := vertex_spans F hF x.property hxj
  let z : GraphVertices F := ⟨z₀,hjxz.vertex_right⟩
  have hxy : x≠y := fun h=>hixy.ne (congrArg Subtype.val h)
  have hxz : x≠z := fun h=>hjxz.ne (congrArg Subtype.val h)
  have hyz : y≠z := by
    intro h
    exact hji (spans_edge_unique F hF (show Spans (F j) x.val y.val from
      (congrArg Subtype.val h).symm ▸ hjxz) hixy)
  have memS {a:ι} (ha:a∈regionEdges F ConnectedComponents.mk out) {v:GraphVertices F}
      (hv:v.val∈range (F a)) : v∈S :=
    (mem_faceVertices F out v.val).mpr ⟨v.property,region_edge_in_closure F hF Q hQ
      ConnectedComponents.continuous_coe ha hv⟩
  have hxS : x∈S := memS hi hixy.mem_left
  have hyS : y∈S := memS hi hixy.mem_right
  have hzS : z∈S := memS hj hjxz.mem_right
  have hfin : faceVertices F out={x.val,y.val,z.val} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption
    · rw [hthree]
      have hxy' : x.val≠y.val := fun h=>hxy (Subtype.ext h)
      have hxz' : x.val≠z.val := fun h=>hxz (Subtype.ext h)
      have hyz' : y.val≠z.val := fun h=>hyz (Subtype.ext h)
      simp [hxy',hxz',hyz']
  have hS : S={x,y,z} := by
    ext v
    simp only [S,mem_ofPred_eq,hfin,Finset.mem_insert,Finset.mem_singleton,
      mem_insert_iff,mem_singleton_iff,Subtype.val_inj]
  let T : Set ι := {i,j}
  have hTend {u v:GraphVertices F} (h:(edgeGraph F T).Adj u v) :
      (u=x ∧ (v=y ∨ v=z)) ∨ (v=x ∧ (u=y ∨ u=z)) := by
    obtain ⟨k,hk,hksp⟩ := h
    rcases hk with rfl|rfl
    · rcases hixy.endpoints_eq hksp with h|h
      · exact Or.inl ⟨Subtype.ext h.1,Or.inl (Subtype.ext h.2)⟩
      · exact Or.inr ⟨Subtype.ext h.2,Or.inl (Subtype.ext h.1)⟩
    · rcases hjxz.endpoints_eq hksp with h|h
      · exact Or.inl ⟨Subtype.ext h.1,Or.inr (Subtype.ext h.2)⟩
      · exact Or.inr ⟨Subtype.ext h.2,Or.inr (Subtype.ext h.1)⟩
  have hTstar : edgeGraph F T≤SimpleGraph.starGraph x := by
    intro u v h
    apply SimpleGraph.starGraph_adj.mpr
    exact ⟨h.ne,(hTend h).elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)⟩
  refine ⟨T,(SimpleGraph.isAcyclic_starGraph x).anti hTstar,?_,?_,?_⟩
  · have reach (v:S) : ((edgeGraph F T).induce S).Reachable ⟨x,hxS⟩ v := by
      have hv : v.val∈({x,y,z}:Set (GraphVertices F)) := by simpa only [hS] using v.property
      rcases hv with hv|hv|hv
      · have he : v=⟨x,hxS⟩ := Subtype.ext hv
        rw [he]
      · have he : v=⟨y,hyS⟩ := Subtype.ext hv
        rw [he]
        exact (show ((edgeGraph F T).induce S).Adj ⟨x,hxS⟩ ⟨y,hyS⟩ from
          ⟨i,Or.inl rfl,hixy⟩).reachable
      · have he : v=⟨z,hzS⟩ := Subtype.ext hv
        rw [he]
        exact (show ((edgeGraph F T).induce S).Adj ⟨x,hxS⟩ ⟨z,hzS⟩ from
          ⟨j,Or.inr rfl,hjxz⟩).reachable
    exact fun u v=>(reach u).symm.trans (reach v)
  · intro u v h
    rcases hTend h with ⟨rfl,hv⟩|⟨rfl,hu⟩
    · exact ⟨hxS,hv.elim (fun h=>h ▸ hyS) (fun h=>h ▸ hzS)⟩
    · exact ⟨hu.elim (fun h=>h ▸ hyS) (fun h=>h ▸ hzS),hxS⟩
  · intro k hk₀ hk₁
    let u : GraphVertices F := ⟨F k 0,⟨k,Or.inl rfl⟩⟩
    let v : GraphVertices F := ⟨F k 1,⟨k,Or.inr rfl⟩⟩
    have huv : u≠v := fun he=>(F k).endpoints_ne (congrArg Subtype.val he)
    have huS : u∈S := hk₀
    have hvS : v∈S := hk₁
    let G := edgeGraph F (regionEdges F ConnectedComponents.mk out)
    have every_neighbor {p:GraphVertices F} (hp:p∈S) :
        ∃ w,G.Adj p w := by
      rw [hS] at hp
      rcases hp with rfl|rfl|rfl
      · exact ⟨y,i,hi,hixy⟩
      · exact ⟨x,i,hi,hixy.symm⟩
      · exact ⟨x,j,hj,hjxz.symm⟩
    obtain ⟨w,hw⟩ := every_neighbor huS
    obtain ⟨a,b,hab,heq⟩ := Set.ncard_eq_two.mp
      (facial_graph_isCycles F hF Q hQ hK out (show (G.neighborSet u).Nonempty from ⟨w,hw⟩))
    have ha : G.Adj u a := by
      change a∈G.neighborSet u
      rw [heq]
      exact Or.inl rfl
    have hb : G.Adj u b := by
      change b∈G.neighborSet u
      rw [heq]
      exact Or.inr rfl
    have haS : a∈S := by obtain ⟨e,he,hsp⟩ := ha; exact memS he hsp.mem_right
    have hbS : b∈S := by obtain ⟨e,he,hsp⟩ := hb; exact memS he hsp.mem_right
    have hvab : v=a ∨ v=b := by
      by_contra hn
      push Not at hn
      have hsCard : S.ncard=3 := by rw [hS]; simp [hxy,hxz,hyz]
      have hsu : ({u,v,a,b}:Set (GraphVertices F))⊆S := by
        intro p hp; rcases hp with rfl|rfl|rfl|rfl <;> assumption
      have hc := Set.ncard_le_ncard hsu (Set.toFinite S)
      have hua : u≠a := ha.ne
      have hub : u≠b := hb.ne
      have hc4 : ({u,v,a,b}:Set (GraphVertices F)).ncard=4 := by
        simp [huv,hua,hub,hn.1,hn.2,hab]
      rw [hc4,hsCard] at hc
      omega
    have hvG : G.Adj u v := hvab.elim (fun h=>h ▸ ha) (fun h=>h ▸ hb)
    obtain ⟨e,he,hsp⟩ := hvG
    have hek := spans_edge_unique F hF hsp (show Spans (F k) u.val v.val from Or.inl ⟨rfl,rfl⟩)
    exact hek ▸ he

theorem triangular_disk_gauge_integrates (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (out:Faces F) (hthree:(faceVertices F out).card=3)
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (K : ι→D)
    (hflat : ∀ q,Vertex F q → q∉faceVertices F out → ∃ t : Faces F→D,
      ∀ j,q∈range (F j) → K j*t (a j)=t (b j)) :
    ∃ v : Faces F→D,∀ i,a i≠out → b i≠out → K i*v (a i)=v (b i) := by
  classical
  obtain ⟨T,hTa,hTc,hTS,hchord⟩ := triangular_face_scaffold F hF Q hQ hK out hthree
  obtain ⟨v,hv⟩ := planar_disk_gauge_integrates F hF Q hQ hK a b hab ha hb T hTa
    {x | x.val∈faceVertices F out} hTc hTS K (fun q hq=>hflat q q.property hq)
  refine ⟨v,fun i hai hbi=>hv i ?_⟩
  by_contra hn
  push Not at hn
  have hi := hchord i hn.1 hn.2
  rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hi with h|h
  · exact hai h.symm
  · exact hbi h.symm
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
