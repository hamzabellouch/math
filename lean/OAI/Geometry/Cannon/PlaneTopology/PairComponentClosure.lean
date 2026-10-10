import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Spans

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
namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

lemma pair_component_closure (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (P : Finset (ℂ × ℂ)) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2)
    {x : ℂ} (hx : x∉range a∪range b) :
    closure (connectedComponentIn (range a∪range b)ᶜ x)=
      connectedComponentIn (range a∪range b)ᶜ x∪(range a∪range b) := by
  let C := range a∪range b
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Cᶜ : Set ℂ) := hC.isOpen_compl.locallyConnectedSpace
  let d : ConnectedComponents (Cᶜ : Set ℂ) := ConnectedComponents.mk ⟨x,hx⟩
  have he : region Cᶜ ConnectedComponents.mk d=connectedComponentIn Cᶜ x := component_region_eq _ ⟨x,hx⟩
  rw [←he]
  obtain ⟨l,hl⟩ := tame_pair_jordan a b h₀ h₁ hc P ha hb
  apply Subset.antisymm
  · intro z hz
    by_cases hzC : z∈C
    · exact Or.inr hzC
    · exact Or.inl (closure_region_inside hC.isOpen_compl ConnectedComponents.continuous_coe hz hzC)
  · apply union_subset subset_closure
    intro z hz
    show d∈incident Cᶜ ConnectedComponents.mk z
    rw [hl z hz]
    exact l.surjective d

theorem isolated_jordan_face {K T : Set ℂ} (hKclosed : IsClosed K) (hK : IsPreconnected K)
    (hT : IsClosed T) (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (P : Finset (ℂ × ℂ)) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hCK : range a∪range b⊆K) (hCT : Disjoint (range a∪range b) T)
    {x : ℂ} (hx : x∉K)
    (hcl : closure (connectedComponentIn Kᶜ x)=connectedComponentIn Kᶜ x∪((range a∪range b)∪T)) :
    frontier (connectedComponentIn Kᶜ x)=range a∪range b ∧
      closure (connectedComponentIn Kᶜ x)=connectedComponentIn Kᶜ x∪(range a∪range b) := by
  let C := range a∪range b
  let U := connectedComponentIn Kᶜ x
  let R := connectedComponentIn Cᶜ x
  have hC : IsClosed C := a.compact_range.isClosed.union b.compact_range.isClosed
  have hxC : x∉C := fun h => hx (hCK h)
  have hUopen : IsOpen U := hKclosed.isOpen_compl.connectedComponentIn
  have hRopen : IsOpen R := hC.isOpen_compl.connectedComponentIn
  have hRconn : IsConnected R := isConnected_connectedComponentIn_iff.mpr hxC
  have hUsub : U⊆Kᶜ := connectedComponentIn_subset _ _
  have hRsub : R⊆Cᶜ := connectedComponentIn_subset _ _
  have hUR : U⊆R := isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx) (fun z hz => fun h => hUsub hz (hCK h))
  have hRcl : closure R=R∪C := pair_component_closure a b h₀ h₁ hc P ha hb hxC
  have hCcl : C⊆closure U := by intro q hq; rw [hcl]; exact Or.inr (Or.inl hq)
  have hfree (q : ℂ) (hq : q∈C) : q∉closure (K∩R) := by
    obtain ⟨r,hr,hloc⟩ := pair_component_local_access a b h₀ h₁ hc P ha hb hq
    have hqT : q∉T := disjoint_left.mp hCT hq
    obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hqT)
    let s := min r δ
    have hs : 0<s := lt_min hr hδ
    have hconn : IsPreconnected (R∩ball q s) := hloc s hs (min_le_left ..) x
    have hball : ball q s⊆Tᶜ := (ball_subset_ball (min_le_right ..)).trans hδT
    have hcover : R∩ball q s⊆U∪(closure U)ᶜ := by
      intro z hz
      by_cases hzU : z∈U
      · exact Or.inl hzU
      · refine Or.inr ?_
        rw [hcl]
        exact fun h => h.elim hzU (fun h => h.elim (hRsub hz.1) (hball hz.2))
    have hdis : Disjoint U (closure U)ᶜ := disjoint_left.mpr (fun z hz hn => hn (subset_closure hz))
    obtain ⟨z,hzB,hzU⟩ := (mem_closure_iff_nhds.mp (hCcl hq)) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
    have hsub : R∩ball q s⊆U := hconn.subset_left_of_subset_union hUopen isClosed_closure.isOpen_compl
      hdis hcover ⟨z,⟨hUR hzU,hzB⟩,hzU⟩
    intro hqKR
    obtain ⟨z,hzB,hzK,hzR⟩ := (mem_closure_iff_nhds.mp hqKR) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
    exact hUsub (hsub ⟨hzR,hzB⟩) hzK
  have hKRclosed : IsClosed (K∩R) := by
    apply isClosed_of_closure_subset
    intro z hz
    have hzK : z∈K := hKclosed.closure_subset_iff.mpr inter_subset_left hz
    have hzclR : z∈closure R := closure_mono inter_subset_right hz
    rw [hRcl] at hzclR
    exact ⟨hzK,hzclR.resolve_right (fun hzC => hfree z hzC hz)⟩
  have hRfree : R⊆Kᶜ := by
    intro z hzR hzK
    have haC : a 0∈C := Or.inl (mem_range_self 0)
    obtain ⟨w,-,hwKR,hwR⟩ := (isPreconnected_closed_iff.mp hK) (K∩R) Rᶜ hKRclosed hRopen.isClosed_compl
      (by intro y hy; by_cases hyR : y∈R; exact Or.inl ⟨hy,hyR⟩; exact Or.inr hyR)
      ⟨z,hzK,hzK,hzR⟩ ⟨a 0,hCK haC,fun h => hRsub h haC⟩
    exact hwR hwKR.2
  have hRU : R⊆U := hRconn.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hxC) hRfree
  have hUR' : U=R := Subset.antisymm hUR hRU
  have hcl' : closure U=U∪C := by rw [hUR',hRcl]
  refine ⟨?_,hcl'⟩
  rw [frontier,hUopen.interior_eq,hcl']
  ext z
  constructor
  · rintro ⟨h,hn⟩
    exact h.resolve_left hn
  · intro hz
    exact ⟨Or.inr hz,fun h => hUsub h (hCK hz)⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma walk_edge_mem (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) {i : ι} (hi : edgeKey F i∈w.edges) : i∈E := by
  have h := w.edges_subset_edgeSet hi
  change (edgeGraph F E).Adj (edgeStart F i) (edgeEnd F i) at h
  obtain ⟨j,hj,hji⟩ := h
  have he : j=i := spans_edge_unique F hF hji (Or.inl ⟨rfl,rfl⟩)
  exact he ▸ hj

lemma walkCarrier_edgeUnion (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) :
    walkCarrier F w⊆⋃ i∈E,range (F i) := by
  rintro z ⟨i,hi,hzi⟩
  exact mem_iUnion₂.mpr ⟨i,walk_edge_mem F hF w hi,hzi⟩

theorem facial_jordan_cycle [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    ∃ (v : GraphVertices F) (p : (edgeGraph F (regionEdges F ConnectedComponents.mk d)).Walk v v)
      (a b : Arc ℂ),p.IsCycle ∧ a 0=b 0 ∧ a 1=b 1 ∧
      (∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      range a∪range b=walkCarrier F p ∧
      frontier (face F d)=range a∪range b ∧
      closure (face F d)=face F d∪(range a∪range b) := by
  classical
  let K := ⋃ i,range (F i)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hKclosed.isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let G := edgeGraph F E
  have hG : G.IsCycles := facial_graph_isCycles F hF P hP hK d
  obtain ⟨i,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge F hF ConnectedComponents.continuous_coe d (face_nonempty F d)
  have hi : i∈E := ⟨t,ht₀,ht₁,ht⟩
  have hne : (G.neighborSet (edgeStart F i)).Nonempty := ⟨edgeEnd F i,i,hi,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨p,hp,-⟩ := hG.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c:=G.connectedComponentMk (edgeStart F i)) (show edgeStart F i∈(G.connectedComponentMk (edgeStart F i)).supp from rfl) hne
  obtain ⟨a,b,h₀,h₁,hc,hC⟩ := simple_cycle_arcs F hF p hp
  let T := ⋃ j∈{j∈E | edgeKey F j∉p.edges},range (F j)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => (F j).compact_range.isClosed
  have hB : (⋃ j∈E,range (F j))=(range a∪range b)∪T := by
    rw [hC]
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
      by_cases hjp : edgeKey F j∈p.edges
      · exact Or.inl ⟨j,hjp,hzj⟩
      · exact Or.inr (mem_iUnion₂.mpr ⟨j,⟨hj,hjp⟩,hzj⟩)
    · apply union_subset (walkCarrier_edgeUnion F hF p)
      intro z hz
      obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨j,hj.1,hzj⟩
  have hCT : Disjoint (range a∪range b) T := hC ▸ cycle_edges_isolated F hF hG p hp
  have hCK : range a∪range b⊆K := hC ▸ walkCarrier_subset F p
  have hseg : (range a∪range b)⊆⋃ p∈P,segment ℝ p.1 p.2 := by
    intro z hz
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hCK hz)
    exact hP j hj
  obtain ⟨x,hxd⟩ := ConnectedComponents.surjective_coe d
  have hface : face F d=connectedComponentIn Kᶜ x.val := by
    change region Kᶜ ConnectedComponents.mk d=_
    rw [←hxd,component_region_eq]
  have hconn : IsPreconnected K := by
    have he : K\{x.val}=K := sdiff_singleton_eq_self x.property
    exact he ▸ hK x.val
  have hwhole := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  rw [hB] at hwhole
  have hh := isolated_jordan_face hKclosed hconn hT a b h₀ h₁ hc P
    (subset_union_left.trans hseg) (subset_union_right.trans hseg) hCK hCT x.property (hface ▸ hwhole)
  rw [←hface] at hh
  exact ⟨edgeStart F i,p,a,b,hp,h₀,h₁,hc,hC,hh.1,hh.2⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma facial_boundary_preconnected [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    IsPreconnected (frontier (face F d)) := by
  obtain ⟨v,p,a,b,hp,h₀,h₁,hc,hC,hfront,hcl⟩ := facial_jordan_cycle F hF P hP hK d
  rw [hfront]
  exact IsPreconnected.union' ⟨a 0,mem_range_self 0,⟨0,h₀.symm⟩⟩
    (isPreconnected_range a.continuous) (isPreconnected_range b.continuous)

lemma third_facial_edge_impossible (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    {i j k : ι} (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hi : i∈regionEdges F ConnectedComponents.mk d)
    (hj : j∈regionEdges F ConnectedComponents.mk d)
    (hk : k∈regionEdges F ConnectedComponents.mk d)
    {q : ℂ} (hq : Vertex F q) (hqi : q∈range (F i))
    (hqj : q∈range (F j)) (hqk : q∈range (F k)) : False := by
  apply noncut_face_degree_two F hF P hP hq (hK q) d ![i,j,k]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro parameter; fin_cases parameter <;> assumption
  · intro parameter; fin_cases parameter <;> assumption

theorem triangle_whole_face [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    (S : Finset ι) (hS : S.Nonempty)
    (hface : ∀ i∈S,i∈regionEdges F ConnectedComponents.mk d)
    (hsecond : ∀ i∈S,∀ t:I,t=0 ∨ t=1 → ∃ j∈S,j≠i ∧ F i t∈range (F j)) :
    frontier (face F d)=⋃ i∈S,range (F i) ∧
      closure (face F d)=face F d∪⋃ i∈S,range (F i) := by
  classical
  let K := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let C := ⋃ i∈S,range (F i)
  let T := ⋃ i∈E\(S : Set ι),range (F i)
  have hCc : IsClosed C := isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  have hTc : IsClosed T := isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  have hCT : Disjoint C T := by
    apply disjoint_left.mpr
    intro q hqC hqT
    obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hqC
    obtain ⟨k,hk,u,huk⟩ := mem_iUnion₂.mp hqT
    have hki : k≠i := fun h => hk.2 (h ▸ hi)
    have ht := ((hF hki).1 u t huk).2
    obtain ⟨j,hj,hji,hqj⟩ := hsecond i hi t ht
    have hkj : k≠j := fun h => hk.2 (h ▸ hj)
    exact third_facial_edge_impossible F hF P hP hK d hji.symm hki.symm hkj.symm
      (hface i hi) (hface j hj) hk.1
      ⟨i,ht.elim (fun h => Or.inl (congrArg (F i) h).symm) (fun h => Or.inr (congrArg (F i) h).symm)⟩
      (mem_range_self t) hqj ⟨u,huk⟩
  have hcl : closure (face F d)=face F d∪(C∪T) := by
    have hh : closure (face F d)=face F d∪⋃ i∈E,range (F i) := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
    rw [hh]
    congr 1
    ext z
    constructor
    · intro h
      obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp h
      by_cases hiS : i∈S
      · exact Or.inl (mem_iUnion₂.mpr ⟨i,hiS,hzi⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨i,⟨hi,hiS⟩,hzi⟩)
    · rintro (h|h)
      · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp h
        exact mem_iUnion₂.mpr ⟨i,hface i hi,hzi⟩
      · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp h
        exact mem_iUnion₂.mpr ⟨i,hi.1,hzi⟩
  have hCK : C∪T⊆K := by
    rintro z (h|h) <;> obtain ⟨i,-,hzi⟩ := mem_iUnion₂.mp h <;> exact mem_iUnion.mpr ⟨i,hzi⟩
  have hfront : frontier (face F d)=C∪T := by
    rw [frontier,(face_open F d).interior_eq,hcl]
    ext z
    constructor
    · rintro ⟨h,hn⟩; exact h.resolve_left hn
    · intro h; exact ⟨Or.inr h,fun hz => hz.1 (hCK h)⟩
  have hBC : C∪T⊆C := by
    have hp := facial_boundary_preconnected F hF P hP hK d
    rw [hfront] at hp
    obtain ⟨i,hi⟩ := hS
    have hh := (isPreconnected_closed_iff.mp hp) C T hCc hTc Subset.rfl
      ⟨F i 0,Or.inl (mem_iUnion₂.mpr ⟨i,hi,mem_range_self 0⟩),mem_iUnion₂.mpr ⟨i,hi,mem_range_self 0⟩⟩
    intro z hz
    by_contra hn
    obtain ⟨y,-,hyC,hyT⟩ := hh ⟨z,hz,hz.resolve_left hn⟩
    exact disjoint_left.mp hCT hyC hyT
  have he : C∪T=C := Subset.antisymm hBC subset_union_left
  exact ⟨hfront.trans he,by simpa only [he] using hcl⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι κ : Type*} [Finite ι] [Finite κ]

theorem refined_face_new_edge (G : κ → Arc ℂ)
    (hG : Pairwise (fun i j => Compatible (G i) (G j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (G i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces G) {K U : Set ℂ} (hUK : U⊆Kᶜ) (hVU : face G d⊆U)
    {q : ℂ} (hq : q∈closure (face G d))
    (hloc : ∃ r : ℝ,0<r ∧ ∀ s,0<s → s≤r → IsPreconnected (U∩ball q s))
    (hacc : q∈closure (U∩(⋃ i,range (G i)))) :
    ∃ j,j∈regionEdges G ConnectedComponents.mk d ∧ q∈range (G j) ∧ ¬range (G j)⊆K := by
  classical
  let L := ⋃ i,range (G i)
  let _ : LocallyConnectedSpace (Lᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (G i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let V := face G d
  let E := regionEdges G ConnectedComponents.mk d
  let T := ⋃ j∈{j∈E | q∉range (G j)},range (G j)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => (G j).compact_range.isClosed
  have hqT : q∉T := by
    intro h
    obtain ⟨j,hj,hqj⟩ := mem_iUnion₂.mp h
    exact hj.2 hqj
  by_contra hn
  have hjK (j : κ) (hj : j∈E) (hqj : q∈range (G j)) : range (G j)⊆K := by
    by_contra hn'
    exact hn ⟨j,hj,hqj,hn'⟩
  obtain ⟨r,hr,hloc⟩ := hloc
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hqT)
  let s := min r δ
  have hs : 0<s := lt_min hr hδ
  have hball : ball q s⊆Tᶜ := (ball_subset_ball (min_le_right ..)).trans hδT
  have hcl : closure V=V∪⋃ j∈E,range (G j) := tame_region_closure G hG P hP ConnectedComponents.continuous_coe d
  have hcover : U∩ball q s⊆V∪(closure V)ᶜ := by
    intro z hz
    by_cases hzV : z∈V
    · exact Or.inl hzV
    · refine Or.inr ?_
      rw [hcl]
      rintro (h|h)
      · exact hzV h
      · obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp h
        by_cases hqj : q∈range (G j)
        · exact hUK hz.1 (hjK j hj hqj hzj)
        · exact hball hz.2 (mem_iUnion₂.mpr ⟨j,⟨hj,hqj⟩,hzj⟩)
  obtain ⟨z,hzB,hzV⟩ := (mem_closure_iff_nhds.mp hq) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
  have hUV : U∩ball q s⊆V := (hloc s hs (min_le_left ..)).subset_left_of_subset_union
    (face_open G d) isClosed_closure.isOpen_compl
    (disjoint_left.mpr fun _ h hn => hn (subset_closure h)) hcover ⟨z,⟨hVU hzV,hzB⟩,hzV⟩
  obtain ⟨z,hzB,hzU,hzL⟩ := (mem_closure_iff_nhds.mp hacc) (ball q s) (isOpen_ball.mem_nhds (mem_ball_self hs))
  exact (hUV ⟨hzU,hzB⟩).1 hzL

lemma face_local_access (F : ι → Arc ℂ)
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : q∈⋃ i,range (F i))
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    ∃ r : ℝ,0<r ∧ ∀ s,0<s → s≤r → IsPreconnected (face F d∩ball q s) := by
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  have hconn : IsConnected ((⋃ i,range (F i))\{q}) := by
    obtain ⟨z,hz,-,hzq⟩ := graph_no_isolated F hq isOpen_univ (mem_univ _)
    exact ⟨⟨z,hz,hzq⟩,hK⟩
  rw [hQ] at hq hconn
  obtain ⟨r,hr,hloc⟩ := noncut_locally_connected_faces Q hq hconn
  refine ⟨r,hr,fun s hs hsr => ?_⟩
  obtain ⟨x,hx⟩ := ConnectedComponents.surjective_coe d
  have hh := hloc s hs hsr x.val
  rw [←hQ] at hh
  simpa only [face,←hx,component_region_eq] using hh

lemma arc_endpoint_closure_interior {X : Type*} [TopologicalSpace X] (a : Arc X) :
    a 1∈closure (a '' Ioo (0:I) 1) := by
  have h : (1:I)∈closure (Ioo (0:I) 1) := by rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one,le_rfl⟩
  exact image_closure_subset_closure_image a.continuous ⟨1,h,rfl⟩

theorem spoke_forces_new_facial_edge (F : ι → Arc ℂ)
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (G : κ → Arc ℂ) (hG : Pairwise (fun i j => Compatible (G i) (G j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (G i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (d : Faces F) (e : Faces G) (hsub : face G e⊆face F d)
    (a : Arc ℂ) (ha : a '' Ioo (0:I) 1⊆face F d) (haG : range a⊆⋃ i,range (G i))
    (haK : a 1∈⋃ i,range (F i)) (hK : IsPreconnected ((⋃ i,range (F i))\{a 1}))
    (hq : a 1∈closure (face G e)) :
    ∃ j,j∈regionEdges G ConnectedComponents.mk e ∧ a 1∈range (G j) ∧
      ¬range (G j)⊆⋃ i,range (F i) := by
  apply refined_face_new_edge G hG Q hQ e (fun _ h => h.1) hsub hq (face_local_access F P hP haK hK d)
  apply closure_mono _ (arc_endpoint_closure_interior a)
  intro z hz
  exact ⟨ha hz,haG (image_subset_range _ _ hz)⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι κ : Type*}

lemma face_parent [Finite ι] [Finite κ] (F : ι → Arc ℂ) (G : κ → Arc ℂ)
    (hFG : (⋃ i,range (F i))⊆⋃ i,range (G i)) (e : Faces G) :
    ∃ d : Faces F,face G e⊆face F d := by
  obtain ⟨x,hx⟩ := face_nonempty G e
  have hxF : x∉⋃ i,range (F i) := fun h => hx.1 (hFG h)
  let d : Faces F := ConnectedComponents.mk ⟨x,hxF⟩
  refine ⟨d,?_⟩
  have hconn := (component_region_connected (⋃ i,range (G i))ᶜ e).isPreconnected
  have hsub : face G e⊆(⋃ i,range (F i))ᶜ := fun z hz h => hz.1 (hFG h)
  have hh := hconn.subset_connectedComponentIn hx hsub
  simpa only [face,d,component_region_eq] using hh

lemma same_face_of_mem_closure [Finite ι] (F : ι → Arc ℂ) {d e : Faces F} {z : ℂ}
    (hz : z∈face F d) (he : z∈closure (face F e)) : d=e := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hh := closure_region_inside
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl
    ConnectedComponents.continuous_coe he hz.1
  exact hz.2.symm.trans hh.2

lemma stellar_spoke_parent [Finite ι] (F : ι → Arc ℂ) [Finite (Faces F)]
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d)
    {i : Σ d : Faces F,faceVertices F d}
    (hi : Sum.inr i∈regionEdges (Sum.elim F A) ConnectedComponents.mk e) : i.1=d := by
  let G := Sum.elim F A
  let _ : LocallyConnectedSpace ((⋃ j,range (G j))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun j => (G j).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hcl := region_edge_in_closure G hG Q hQ ConnectedComponents.continuous_coe hi
  obtain ⟨parameter,_,hlt,_⟩ := hi
  have hpoint : A i parameter∈closure (face F d) :=
    closure_mono hsub (hcl (mem_range_self parameter))
  exact same_face_of_mem_closure F
    (fan_parameter_in_face (h₀ i ▸ hc i.1) (hU i) (ne_of_lt hlt)) hpoint

lemma stellar_old_endpoint [Finite ι] (F : ι → Arc ℂ)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    {q : ℂ} (hq : q∈⋃ j,range (F j)) {i : Σ d : Faces F,faceVertices F d}
    (hi : q∈range (A i)) : q=i.2.val := by
  obtain ⟨t,ht⟩ := hi
  have ht1 : t=1 := by
    by_contra hn
    exact (fan_parameter_in_face (h₀ i ▸ hc i.1) (hU i) hn).1 (ht ▸ hq)
  exact ht.symm.trans (ht1 ▸ h₁ i)

theorem stellar_old_vertex_spoke_facial [Finite ι] (F : ι → Arc ℂ) [Finite (Faces F)]
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d)
    (v : faceVertices F d) (hv : v.val∈closure (face (Sum.elim F A) e)) :
    Sum.inr ⟨d,v⟩∈regionEdges (Sum.elim F A) ConnectedComponents.mk e := by
  have hvK := vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1
  obtain ⟨j,hj,hvj,hjK⟩ := spoke_forces_new_facial_edge F P hP (Sum.elim F A) hG Q hQ d e hsub
    (A ⟨d,v⟩) (hU ⟨d,v⟩) (subset_iUnion (fun i => range (Sum.elim F A i : Arc ℂ)) (Sum.inr ⟨d,v⟩))
    (h₁ ⟨d,v⟩ ▸ hvK) (hK _) (h₁ ⟨d,v⟩ ▸ hv)
  rcases j with j|⟨d',v'⟩
  · exact (hjK (subset_iUnion (fun i => range (F i)) j)).elim
  · have hd' : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hj
    subst d'
    have hv' : v'=v := Subtype.ext (by
      have hh := stellar_old_endpoint F c A hc h₀ h₁ hU hvK (show v.val∈range (A ⟨d,v'⟩) by simpa only [h₁,Sum.elim_inr] using hvj)
      exact hh.symm)
    simpa only [hv'] using hj

lemma stellar_face_old_edge [Finite ι] (F : ι → Arc ℂ) [Nonempty ι] [Finite (Faces F)]
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q}))
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d) :
    ∃ i : ι,Sum.inl i∈regionEdges (Sum.elim F A) ConnectedComponents.mk e := by
  let G := Sum.elim F A
  let _ : LocallyConnectedSpace ((⋃ i,range (G i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (G i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨j,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge G hG ConnectedComponents.continuous_coe e (face_nonempty G e)
  have hj : j∈regionEdges G ConnectedComponents.mk e := ⟨t,ht₀,ht₁,ht⟩
  rcases j with i|⟨d',v⟩
  · exact ⟨i,hj⟩
  · have hd : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hj
    subst d'
    have hvK := vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1
    have hvG : Vertex G v.val := ⟨Sum.inr ⟨d,v⟩,Or.inr (h₁ ⟨d,v⟩)⟩
    obtain ⟨k,hkj,hk,hvk⟩ := noncut_face_second_edge G hG Q hQ hK e hvG hj ⟨1,h₁ ⟨d,v⟩⟩
    rcases k with i|⟨d',w⟩
    · exact ⟨i,hk⟩
    · have hd : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hk
      subst d'
      have hvw : v=w := Subtype.ext (stellar_old_endpoint F c A hc h₀ h₁ hU hvK hvk)
      exact (hkj (by rw [hvw])).elim

end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem stellar_face_triangle (F : ι → Arc ℂ) [Finite (Faces F)]
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hGK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q}))
    (e : Faces (Sum.elim F A)) :
    ∃ (d : Faces F) (i : ι) (v w : faceVertices F d),
      F i 0=v.val ∧ F i 1=w.val ∧ v≠w ∧
      face (Sum.elim F A) e⊆face F d ∧
      frontier (face (Sum.elim F A) e)=range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩) ∧
      closure (face (Sum.elim F A) e)=face (Sum.elim F A) e∪
        (range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩)) := by
  classical
  let G := Sum.elim F A
  let _ : LocallyConnectedSpace ((⋃ i,range (G i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (G i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hFG : (⋃ i,range (F i))⊆⋃ i,range (G i) := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨Sum.inl i,hi⟩
  obtain ⟨d,hsub⟩ := face_parent F G hFG e
  obtain ⟨i,hi⟩ := stellar_face_old_edge F c A hc h₀ h₁ hU hG Q hQ hGK hsub
  have hcl : range (F i)⊆closure (face G e) := region_edge_in_closure G hG Q hQ ConnectedComponents.continuous_coe hi
  have hv : F i 0∈faceVertices F d := (mem_faceVertices F d _).mpr
    ⟨⟨i,Or.inl rfl⟩,closure_mono hsub (hcl (mem_range_self 0))⟩
  have hw : F i 1∈faceVertices F d := (mem_faceVertices F d _).mpr
    ⟨⟨i,Or.inr rfl⟩,closure_mono hsub (hcl (mem_range_self 1))⟩
  let v : faceVertices F d := ⟨F i 0,hv⟩
  let w : faceVertices F d := ⟨F i 1,hw⟩
  have hvw : v≠w := fun h => (F i).endpoints_ne (congrArg Subtype.val h)
  have hvf := stellar_old_vertex_spoke_facial F P hP hK c A hc h₀ h₁ hU hG Q hQ hsub v (hcl (mem_range_self 0))
  have hwf := stellar_old_vertex_spoke_facial F P hP hK c A hc h₀ h₁ hU hG Q hQ hsub w (hcl (mem_range_self 1))
  let k : ι ⊕ (Σ d : Faces F,faceVertices F d) := Sum.inl i
  let j : ι ⊕ (Σ d : Faces F,faceVertices F d) := Sum.inr ⟨d,v⟩
  let l : ι ⊕ (Σ d : Faces F,faceVertices F d) := Sum.inr ⟨d,w⟩
  have hjl : j≠l := by
    intro he
    have hh : (⟨d,v⟩ : Σ d : Faces F,faceVertices F d)=⟨d,w⟩ := Sum.inr.inj he
    exact (F i).endpoints_ne (congrArg (fun z : Σ d : Faces F,faceVertices F d => z.2.val) hh)
  let S : Finset (ι ⊕ (Σ d : Faces F,faceVertices F d)) := {k,j,l}
  have hS : S.Nonempty := ⟨k,by simp [S]⟩
  have hSf : ∀ x∈S,x∈regionEdges G ConnectedComponents.mk e := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact hi
    · exact hvf
    · exact hwf
  have hsecond : ∀ x∈S,∀ t:I,t=0 ∨ t=1 → ∃ y∈S,y≠x ∧ G x t∈range (G y) := by
    intro x hx t ht
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> rcases ht with rfl|rfl
    · exact ⟨j,by simp [S],by simp [j,k],1,h₁ ⟨d,v⟩⟩
    · exact ⟨l,by simp [S],by simp [l,k],1,h₁ ⟨d,w⟩⟩
    · exact ⟨l,by simp [S],hjl.symm,0,(h₀ ⟨d,w⟩).trans (h₀ ⟨d,v⟩).symm⟩
    · exact ⟨k,by simp [S],by simp [j,k],0,(h₁ ⟨d,v⟩).symm⟩
    · exact ⟨j,by simp [S],hjl,0,(h₀ ⟨d,v⟩).trans (h₀ ⟨d,w⟩).symm⟩
    · exact ⟨k,by simp [S],by simp [l,k],1,(h₁ ⟨d,w⟩).symm⟩
  obtain ⟨hfront,hclosure⟩ := triangle_whole_face G hG Q hQ hGK e S hS hSf hsecond
  have hC : (⋃ x∈S,range (G x))=range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩) := by
    simp [S,k,j,l,G,union_assoc]
  exact ⟨d,i,v,w,rfl,rfl,hvw,hsub,hfront.trans hC,by simpa only [hC] using hclosure⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem global_triangular_stellation (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    ∃ (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ),
      (∀ d,c d∈face F d) ∧
      Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)) ∧
      (∀ i,A i 0=c i.1) ∧ (∀ i,A i 1=i.2.val) ∧
      (∀ i,FiniteSupport (range (A i))) ∧
      (∀ i,A i '' Ioo (0:I) 1⊆face F i.1) ∧
      (∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q})) ∧
      ∀ e : Faces (Sum.elim F A),∃ (d : Faces F) (i : ι) (v w : faceVertices F d),
        F i 0=v.val ∧ F i 1=w.val ∧ v≠w ∧
        face (Sum.elim F A) e⊆face F d ∧
        frontier (face (Sum.elim F A) e)=range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩) ∧
        closure (face (Sum.elim F A) e)=face (Sum.elim F A) e∪
          (range (F i)∪range (A ⟨d,v⟩)∪range (A ⟨d,w⟩)) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF P hP
  obtain ⟨z,hz⟩ := (complex_finite_segments_compl_dense P).nonempty
  have hzK : z∉⋃ i,range (F i) := fun h => hz (iUnion_subset hP h)
  have hconn : IsPreconnected (⋃ i,range (F i)) := by
    have he : (⋃ i,range (F i))\{z}=⋃ i,range (F i) := sdiff_singleton_eq_self hzK
    exact he ▸ hK z
  obtain ⟨c,A,hc,hG,h₀,h₁,hS,hU,hGK⟩ := global_stellation_no_cut_points F hF P hP hconn
  have hGK' : ∀ q : ℂ,IsPreconnected ((⋃ i,range (Sum.elim F A i : Arc ℂ))\{q}) := by
    intro q
    simpa only [iUnion_sum,Sum.elim_inl,Sum.elim_inr] using hGK q
  have hGS : ∀ i,FiniteSupport (range (Sum.elim F A i : Arc ℂ)) := by
    rintro (i|i)
    · exact ⟨P,hP i⟩
    · exact hS i
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hGS
  have hQ' : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2 := fun i =>
    (subset_iUnion (fun i => range (Sum.elim F A i : Arc ℂ)) i).trans hQ
  exact ⟨c,A,hc,hG,h₀,h₁,hS,hU,hGK',stellar_face_triangle F P hP hK c A hc h₀ h₁ hU hG Q hQ' hGK'⟩
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

end OAI
