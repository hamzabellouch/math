import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.FaceClosuresCover
import OAI.Geometry.Cannon.PlaneTopology.NoncutCycleFreeRegion
import OAI.Geometry.Cannon.Boundary.UnitCircle

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
open Set unitInterval Topology Metric CannonFaceIncidence CannonCircleBoundary

variable {ι : Type*} [Finite ι]

lemma tame_incident_segment (a : Arc ℂ) (P : Finset (ℂ × ℂ))
    (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2) {q : ℂ} (hq : q=a 0 ∨ q=a 1) :
    ∃ p : ℂ,p≠q ∧ segment ℝ q p⊆range a := by
  have first (a : Arc ℂ) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2) :
      ∃ p : ℂ,p≠a 0 ∧ segment ℝ (a 0) p⊆range a := by
    obtain ⟨t,ht,he⟩ := tame_initial_interval a P ha
    exact ⟨a t,a.injective.ne ht.ne',he ▸ image_subset_range _ _⟩
  rcases hq with rfl|rfl
  · exact first a ha
  · simpa only [reverse_zero,reverse_range] using first a.reverse (by simpa only [reverse_range] using ha)

lemma radial_mem_segment {q p : ℂ} (hp : p≠q) {s : ℝ}
    (hs : 0 ≤ s) (hsp : s ≤ ‖p-q‖) :
    q+s • (radialDirection q ⟨p,hp⟩:ℂ)∈segment ℝ q p := by
  have hn : 0<‖p-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  rw [segment_eq_image']
  refine ⟨s/‖p-q‖,⟨div_nonneg hs hn.le,(div_le_one hn).mpr hsp⟩,?_⟩
  simp only [radialDirection,smul_smul,div_eq_mul_inv]

theorem noncut_face_degree_two (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q)
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    (e : Fin 3 → ι) (he : Function.Injective e)
    (heq : ∀ k,q∈range (F (e k)))
    (heface : ∀ k,e k∈regionEdges F ConnectedComponents.mk d) : False := by
  classical
  let K : Set ℂ := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hqK : q∈K := vertex_mem_support F hq
  have hep (k : Fin 3) : q=F (e k) 0 ∨ q=F (e k) 1 := by
    obtain ⟨t,ht⟩ := heq k
    have hh := vertex_parameter F hF (e k) (ht.symm ▸ hq)
    exact hh.elim (fun h => Or.inl (h ▸ ht.symm)) (fun h => Or.inr (h ▸ ht.symm))
  choose p hp hps using fun k => tame_incident_segment (F (e k)) P (hP (e k)) (hep k)
  let u : Fin 3 → UnitCircle := fun k => radialDirection q ⟨p k,hp k⟩
  have hn (k : Fin 3) : 0<‖p k-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hp k))
  have hui : Function.Injective u := by
    intro i j hij
    by_contra hne
    let s := min ‖p i-q‖ ‖p j-q‖/2
    have hs : 0<s := half_pos (lt_min (hn i) (hn j))
    have hsi : s≤‖p i-q‖ := (half_le_self (le_of_lt (lt_min (hn i) (hn j)))).trans (min_le_left _ _)
    have hsj : s≤‖p j-q‖ := (half_le_self (le_of_lt (lt_min (hn i) (hn j)))).trans (min_le_right _ _)
    have hz₁ : q+s • (u i:ℂ)∈range (F (e i)) := hps i (radial_mem_segment (hp i) hs.le hsi)
    have hz₂ : q+s • (u i:ℂ)∈range (F (e j)) := by
      rw [hij]
      exact hps j (radial_mem_segment (hp j) hs.le hsj)
    exact radial_ne q (u i) hs ((hF (he.ne hne)).2 ⟨hz₁,hz₂⟩ ⟨heq i,heq j⟩)
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  have hKc : IsConnected (K\{q}) := by
    obtain ⟨z,hz,-,hzq⟩ := graph_no_isolated F hqK isOpen_univ (mem_univ _)
    exact ⟨⟨z,hz,hzq⟩,hK⟩
  have hqQ : q∈⋃ p∈Q,segment ℝ p.1 p.2 := by rw [←hQ]; exact hqK
  have hKQ : IsConnected ((⋃ p∈Q,segment ℝ p.1 p.2)\{q}) := by rw [←hQ]; exact hKc
  obtain ⟨R,hR,hlocal⟩ := noncut_locally_connected_faces Q hqQ hKQ
  let r := min R (min ‖p 0-q‖ (min ‖p 1-q‖ ‖p 2-q‖))
  have hr : 0<r := lt_min hR (lt_min (hn 0) (lt_min (hn 1) (hn 2)))
  have hrR : r≤R := min_le_left _ _
  have hrp (k : Fin 3) : r≤‖p k-q‖ := by
    have hh := min_le_right R (min ‖p 0-q‖ (min ‖p 1-q‖ ‖p 2-q‖))
    fin_cases k
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  let U := face F d∩ball q r
  have hU : IsPreconnected U := by
    obtain ⟨a,ha⟩ := ConnectedComponents.surjective_coe d
    have hh := hlocal r hr hrR a.val
    rw [←hQ] at hh
    simpa only [U,face,←ha,component_region_eq] using hh
  have hUball : U⊆ball q r\{q} := by
    intro z hz
    exact ⟨hz.2,fun heq => hz.1.1 (heq ▸ hqK)⟩
  apply radial_face_degree_two hU hUball u ?_ ?_ hui
  · intro k s hs hsr hz
    exact hz.1.1 (mem_iUnion.mpr ⟨e k,hps k (radial_mem_segment (hp k) hs.le (hsr.le.trans (hrp k)))⟩)
  · intro k
    have hs : 0<r/2 := half_pos hr
    have hsr : r/2<r := half_lt_self hr
    let z := q+(r/2) • (u k:ℂ)
    have hzr : z∈ball q r := by
      have hu : ‖(u k:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp (u k).property
      simpa only [z,mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_pos hs,hu,mul_one] using hsr
    have hzcl : z∈closure (face F d) :=
      region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe (heface k)
        (hps k (radial_mem_segment (hp k) hs.le (hsr.le.trans (hrp k))))
    refine ⟨r/2,hs,?_⟩
    change z∈closure (face F d∩ball q r)
    rw [inter_comm]
    exact isOpen_ball.inter_closure ⟨hzr,hzcl⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*} [Finite ι]

lemma cycle_edge_otherpoint (a b : Arc ℂ) (h₀ : b 0=a 0) (h₁ : b 1=a 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {q : ℂ} (hq : q=a 0 ∨ q=a 1) {W : Set ℂ} (hW : IsOpen W) (hqW : q∈W) :
    ∃ z∈range b,z∈W ∧ z∉range a := by
  have first (t : I) (ht : q=b t) (hqt : t∈closure (Ioo (0:I) 1)) :
      ∃ z∈range b,z∈W ∧ z∉range a := by
    obtain ⟨s,hsW,hs⟩ := (mem_closure_iff_nhds.mp hqt) (b ⁻¹' W)
      ((hW.preimage b.continuous).mem_nhds (show b t∈W from ht ▸ hqW))
    refine ⟨b s,mem_range_self s,hsW,?_⟩
    rintro ⟨u,hu⟩
    exact ((hc u s hu).2).elim hs.1.ne' hs.2.ne
  rcases hq with h|h
  · apply first 0 (h.trans h₀.symm)
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl,zero_le_one⟩
  · apply first 1 (h.trans h₁.symm)
    rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one,le_rfl⟩

theorem noncut_face_second_edge (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (d : Faces F) {q : ℂ} (hq : Vertex F q) {e : ι}
    (he : e∈regionEdges F ConnectedComponents.mk d) (heq : q∈range (F e)) :
    ∃ j : ι,j≠e ∧ j∈regionEdges F ConnectedComponents.mk d ∧ q∈range (F j) := by
  classical
  let K : Set ℂ := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  let B : Set ℂ := ⋃ i∈E,range (F i)
  let T : Set ℂ := ⋃ i∈E\{e},range (F i)
  have hT : IsClosed T := isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun _ => (F i).compact_range.isClosed
  by_contra hn
  push Not at hn
  have hqT : q∉T := by
    intro hh
    obtain ⟨j,hj,hqj⟩ := mem_iUnion₂.mp hh
    exact hn j hj.2 hj.1 hqj
  have hep : q=F e 0 ∨ q=F e 1 := by
    obtain ⟨t,ht⟩ := heq
    have hh := vertex_parameter F hF e (ht.symm ▸ hq)
    exact hh.elim (fun h => Or.inl (h ▸ ht.symm)) (fun h => Or.inr (h ▸ ht.symm))
  have hw : ∃ W : Set ℂ,IsOpen W ∧ q∈W ∧ W⊆Tᶜ ∧ IsConnected (W\range (F e)) := by
    rcases hep with h|h
    · exact h.symm ▸ tame_tip_connected_neighborhood (F e) P (hP e) hT.isOpen_compl (h ▸ hqT)
    · have hh := tame_tip_connected_neighborhood (F e).reverse P
        (by simpa only [reverse_range] using hP e) hT.isOpen_compl
        (by simpa only [reverse_zero] using h ▸ hqT)
      simpa only [reverse_range,reverse_zero,←h] using hh
  obtain ⟨W,hW,hqW,hWT,hconn⟩ := hw
  have hB (z : ℂ) (hz : z∈W\range (F e)) : z∉B := by
    intro hh
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hh
    by_cases hie : i=e
    · exact hz.2 (hie ▸ hzi)
    · exact hWT hz.1 (mem_iUnion₂.mpr ⟨i,⟨hi,hie⟩,hzi⟩)
  have hcl : closure (face F d)=face F d∪B :=
    tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  have hcover : W\range (F e)⊆face F d∪(closure (face F d))ᶜ := by
    intro z hz
    by_cases hzu : z∈face F d
    · exact Or.inl hzu
    · refine Or.inr ?_
      rw [hcl]
      exact fun h => h.elim hzu (hB z hz)
  have hdis : Disjoint (face F d) (closure (face F d))ᶜ :=
    disjoint_left.mpr (fun _ hu hcl => hcl (subset_closure hu))
  have hh := hconn.isPreconnected.subset_or_subset (face_open F d) isClosed_closure.isOpen_compl hdis hcover
  have hqcl : q∈closure (face F d) := region_edge_in_closure F hF P hP
    ConnectedComponents.continuous_coe he heq
  obtain ⟨x,hxW,hxU⟩ := (mem_closure_iff_nhds.mp hqcl) W (hW.mem_nhds hqW)
  have hx : x∈W\range (F e) := ⟨hxW,fun h => hxU.1 (mem_iUnion.mpr ⟨e,h⟩)⟩
  obtain ⟨b,hb₀,hb₁,hbK,-,hbc⟩ := edge_on_tame_cycle F hF P hP hK e
  obtain ⟨z,hzb,hzW,hza⟩ := cycle_edge_otherpoint (F e) b hb₀ hb₁ hbc hep hW hqW
  rcases hh with hh|hh
  · exact (hh ⟨hzW,hza⟩).1 (hbK hzb)
  · exact hh hx (subset_closure hxU)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

def Spans (a : Arc ℂ) (x y : ℂ) : Prop :=
  (a 0=x ∧ a 1=y) ∨ (a 1=x ∧ a 0=y)
lemma Spans.symm {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : Spans a y x := by
  rcases h with h|h
  · exact Or.inr h.symm
  · exact Or.inl h.symm
lemma Spans.mem_left {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : x∈range a := by
  rcases h with h|h
  · exact ⟨0,h.1⟩
  · exact ⟨1,h.1⟩
lemma Spans.mem_right {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : y∈range a := h.symm.mem_left
lemma Spans.ne {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) : x≠y := by
  rcases h with h|h
  · exact h.1 ▸ h.2 ▸ a.endpoints_ne
  · exact h.1 ▸ h.2 ▸ a.endpoints_ne.symm
lemma Spans.vertex_left [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F x :=
  ⟨i,h.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)⟩
lemma Spans.vertex_right [Finite ι] {F : ι → Arc ℂ} {i : ι} {x y : ℂ} (h : Spans (F i) x y) : Vertex F y :=
  h.symm.vertex_left
lemma Spans.other_unique {a : Arc ℂ} {x y z : ℂ} (h : Spans a x y) (h' : Spans a x z) : y=z := by
  rcases h with h|h <;> rcases h' with h'|h'
  · exact h.2.symm.trans h'.2
  · exact (a.endpoints_ne (h.1.trans h'.1.symm)).elim
  · exact (a.endpoints_ne (h'.1.trans h.1.symm)).elim
  · exact h.2.symm.trans h'.2
lemma spans_edge_unique [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {i j : ι} {x y : ℂ}
    (hi : Spans (F i) x y) (hj : Spans (F j) x y) : i=j := by
  by_contra hn
  exact hi.ne ((hF hn).2 ⟨hi.mem_left,hj.mem_left⟩ ⟨hi.mem_right,hj.mem_right⟩)
lemma vertex_spans [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {q : ℂ}
    (hq : Vertex F q) {i : ι} (hi : q∈range (F i)) : ∃ z,Spans (F i) q z := by
  obtain ⟨t,ht⟩ := hi
  rcases vertex_parameter F hF i (ht.symm ▸ hq) with h|h
  · exact ⟨F i 1,Or.inl ⟨h ▸ ht,rfl⟩⟩
  · exact ⟨F i 0,Or.inr ⟨h ▸ ht,rfl⟩⟩

abbrev GraphVertices (F : ι → Arc ℂ) := {z : ℂ // Vertex F z}
instance graphVertices_finite [Finite ι] (F : ι → Arc ℂ) : Finite (GraphVertices F) := (finite_vertex_set F).to_subtype

def edgeGraph (F : ι → Arc ℂ) (E : Set ι) : SimpleGraph (GraphVertices F) where
  Adj x y := ∃ i∈E,Spans (F i) x.val y.val
  symm := by constructor; rintro x y ⟨i,hi,h⟩; exact ⟨i,hi,h.symm⟩
  loopless := by constructor; rintro x ⟨i,_hi,h⟩; exact h.ne rfl

lemma face_edge_eq [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q)
    (hK : IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F)
    {i j k : ι} (hij : i≠j)
    (hi : i∈regionEdges F ConnectedComponents.mk d) (hj : j∈regionEdges F ConnectedComponents.mk d)
    (hk : k∈regionEdges F ConnectedComponents.mk d)
    (hqi : q∈range (F i)) (hqj : q∈range (F j)) (hqk : q∈range (F k)) : k=i ∨ k=j := by
  by_contra hn
  push Not at hn
  let es : Fin 3 → ι := ![i,j,k]
  have hes : Function.Injective es := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [es]
  exact noncut_face_degree_two F hF P hP hq hK d es hes
    (by intro a; fin_cases a <;> assumption)
    (by intro a; fin_cases a <;> assumption)

theorem facial_graph_isCycles [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (d : Faces F) :
    (edgeGraph F (regionEdges F ConnectedComponents.mk d)).IsCycles := by
  intro x ⟨y,i,hi,hiy⟩
  obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF P hP hK d x.property hi hiy.mem_left
  obtain ⟨z,hjz⟩ := vertex_spans F hF x.property hqj
  let z' : GraphVertices F := ⟨z,hjz.vertex_right⟩
  have hyz : y≠z' := by
    intro h
    exact hji (spans_edge_unique F hF (show Spans (F j) x.val y.val from (congrArg Subtype.val h).symm ▸ hjz) hiy)
  apply Set.ncard_eq_two.mpr
  refine ⟨y,z',hyz,?_⟩
  ext w
  constructor
  · rintro ⟨k,hk,hkw⟩
    rcases face_edge_eq F hF P hP x.property (hK x.val) d hji.symm hi hj hk
      hiy.mem_left hqj hkw.mem_left with h|h
    · subst k
      exact Or.inl (Subtype.ext (hkw.other_unique hiy))
    · subst k
      exact Or.inr (Subtype.ext (hkw.other_unique hjz))
  · rintro (rfl|rfl)
    · exact ⟨i,hi,hiy⟩
    · exact ⟨j,hj,hjz⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

def edgeStart (F : ι → Arc ℂ) (i : ι) : GraphVertices F := ⟨F i 0,i,Or.inl rfl⟩
def edgeEnd (F : ι → Arc ℂ) (i : ι) : GraphVertices F := ⟨F i 1,i,Or.inr rfl⟩
def edgeKey (F : ι → Arc ℂ) (i : ι) : Sym2 (GraphVertices F) := s(edgeStart F i,edgeEnd F i)
lemma edgeKey_eq [Finite ι] (F : ι → Arc ℂ) (i : ι) (x y : GraphVertices F) :
    edgeKey F i=s(x,y) ↔ Spans (F i) x.val y.val := by
  simp only [edgeKey,Sym2.eq_iff,Subtype.ext_iff,edgeStart,edgeEnd,Spans]
  tauto

lemma edgeKey_injective [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) : Function.Injective (edgeKey F) := by
  intro i j hij
  exact spans_edge_unique F hF (show Spans (F i) (F i 0) (F i 1) from Or.inl ⟨rfl,rfl⟩)
    ((edgeKey_eq F j (edgeStart F i) (edgeEnd F i)).mp hij.symm)

def walkCarrier (F : ι → Arc ℂ) {E : Set ι} {x y : GraphVertices F}
    (w : (edgeGraph F E).Walk x y) : Set ℂ := {z | ∃ i,edgeKey F i∈w.edges ∧ z∈range (F i)}

lemma walkCarrier_cons [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y z : GraphVertices F} (h : (edgeGraph F E).Adj x y) (w : (edgeGraph F E).Walk y z)
    {i : ι} (hi : Spans (F i) x.val y.val) : walkCarrier F (w.cons h)=range (F i)∪walkCarrier F w := by
  have hk := (edgeKey_eq F i x y).mpr hi
  ext p
  simp only [walkCarrier,mem_ofPred_eq,SimpleGraph.Walk.edges_cons,List.mem_cons,mem_union]
  constructor
  · rintro ⟨j,(hj|hj),hp⟩
    · have he := edgeKey_injective F hF (hj.trans hk.symm)
      exact Or.inl (he ▸ hp)
    · exact Or.inr ⟨j,hj,hp⟩
  · rintro (hp|⟨j,hj,hp⟩)
    · exact ⟨i,Or.inl hk,hp⟩
    · exact ⟨j,Or.inr hj,hp⟩

lemma walkCarrier_vertex [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y q : GraphVertices F} {w : (edgeGraph F E).Walk x y} (hq : q.val∈walkCarrier F w) : q∈w.support := by
  obtain ⟨i,hi,t,ht⟩ := hq
  rcases vertex_parameter F hF i (ht.symm ▸ q.property) with h|h
  · have he : edgeStart F i=q := Subtype.ext ((congrArg (F i) h).symm.trans ht)
    exact he ▸ w.fst_mem_support_of_mem_edges hi
  · have he : edgeEnd F i=q := Subtype.ext ((congrArg (F i) h).symm.trans ht)
    exact he ▸ w.snd_mem_support_of_mem_edges hi

lemma oriented_arc {a : Arc ℂ} {x y : ℂ} (h : Spans a x y) :
    ∃ b : Arc ℂ,b 0=x ∧ b 1=y ∧ range b=range a := by
  rcases h with h|h
  · exact ⟨a,h.1,h.2,rfl⟩
  · exact ⟨a.reverse,by simpa using h.1,by simpa using h.2,a.reverse_range⟩

theorem simple_walk_arc [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x y : GraphVertices F} (w : (edgeGraph F E).Walk x y) (hw : w.IsPath) (hne : x≠y) :
    ∃ a : Arc ℂ,a 0=x.val ∧ a 1=y.val ∧ range a=walkCarrier F w := by
  induction w with
  | nil => exact (hne rfl).elim
  | @cons x v y h w ih =>
    have hed : ∃ i∈E,Spans (F i) x.val v.val := h
    obtain ⟨i,_hi,hix⟩ := hed
    obtain ⟨a,ha₀,ha₁,ha⟩ := oriented_arc hix
    have hw' := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hw
    by_cases hvy : v=y
    · subst y
      have hn : w.Nil := SimpleGraph.Walk.isPath_iff_nil.mp hw'.1
      cases hn
      refine ⟨a,ha₀,ha₁,?_⟩
      rw [walkCarrier_cons F hF _ _ hix,ha]
      simp [walkCarrier]
    · obtain ⟨b,hb₀,hb₁,hb⟩ := ih hw'.1 hvy
      have hmeet : ∀ s t,a s=b t → s=1 ∧ t=0 := by
        intro s t he
        have hbs : b t∈walkCarrier F w := hb ▸ mem_range_self t
        obtain ⟨j,hj,u,hju⟩ := hbs
        have hji : j≠i := by
          intro hji
          subst j
          have hk := (edgeKey_eq F i x v).mpr hix
          exact hw'.2 (w.fst_mem_support_of_mem_edges (hk ▸ hj))
        obtain ⟨r,hr⟩ := ha ▸ (mem_range_self s : a s∈range a)
        have hrj : F i r=F j u := hr.trans (he.trans hju.symm)
        have hre := ((hF hji.symm).1 r u hrj).1
        have hax : a s=x.val ∨ a s=v.val := by
          rcases hre with rfl|rfl <;> rcases hix with hix|hix
          · exact Or.inl (hr.symm.trans hix.1)
          · exact Or.inr (hr.symm.trans hix.2)
          · exact Or.inr (hr.symm.trans hix.2)
          · exact Or.inl (hr.symm.trans hix.1)
        have hav : a s=v.val := hax.resolve_left (by
          intro hx
          apply hw'.2
          apply walkCarrier_vertex F hF (q:=x)
          exact (he.symm.trans hx) ▸ (hb ▸ mem_range_self t))
        exact ⟨a.injective (hav.trans ha₁.symm),b.injective (he.symm.trans (hav.trans hb₀.symm))⟩
      let pa : Path x.val v.val := a.path.cast ha₀.symm ha₁.symm
      let pb : Path v.val y.val := b.path.cast hb₀.symm hb₁.symm
      let c : Arc ℂ := ⟨(pa.trans pb).toContinuousMap,
        trans_injective pa pb a.injective b.injective hmeet⟩
      refine ⟨c,(pa.trans pb).source,(pa.trans pb).target,?_⟩
      change range (pa.trans pb)=_
      rw [Path.trans_range,walkCarrier_cons F hF _ _ hix]
      exact congrArg₂ (·∪·) ha hb
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence

variable {ι : Type*}

lemma walkCarrier_subset [Finite ι] (F : ι → Arc ℂ) {E : Set ι} {x y : GraphVertices F}
    (w : (edgeGraph F E).Walk x y) : walkCarrier F w⊆⋃ i,range (F i) := by
  rintro z ⟨i,-,hi⟩
  exact mem_iUnion.mpr ⟨i,hi⟩

lemma cycle_saturated {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.IsCycles)
    {x : V} (p : G.Walk x x) (hp : p.IsCycle) {v w : V}
    (hv : v∈p.support) (hvw : G.Adj v w) : s(v,w)∈p.edges := by
  have hn : (G.neighborSet v).Nonempty := ⟨w,hvw⟩
  have he : G.neighborSet v=p.toSubgraph.neighborSet v := by
    apply (Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset v) ?_ (Set.toFinite _)).symm
    rw [hG hn,hp.ncard_neighborSet_toSubgraph_eq_two hv]
  apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
  exact (show w∈p.toSubgraph.neighborSet v from he ▸ hvw)

theorem simple_cycle_arcs [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    {x : GraphVertices F} (p : (edgeGraph F E).Walk x x) (hp : p.IsCycle) :
    ∃ a b : Arc ℂ,a 0=b 0 ∧ a 1=b 1 ∧
      (∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      range a∪range b=walkCarrier F p := by
  cases p with
  | nil => exact (hp.not_nil (by simp)).elim
  | @cons x v x h p =>
    have hed : ∃ i∈E,Spans (F i) x.val v.val := h
    obtain ⟨i,_hi,hix⟩ := hed
    obtain ⟨a,ha₀,ha₁,ha⟩ := oriented_arc hix
    have hp' := (p.cons_isCycle_iff h).mp hp
    obtain ⟨c,hc₀,hc₁,hc⟩ := simple_walk_arc F hF p hp'.1 h.ne.symm
    let b := c.reverse
    have hb₀ : b 0=x.val := by simpa only [b,reverse_zero] using hc₁
    have hb₁ : b 1=v.val := by simpa only [b,reverse_one] using hc₀
    have hb : range b=walkCarrier F p := c.reverse_range.trans hc
    refine ⟨a,b,ha₀.trans hb₀.symm,ha₁.trans hb₁.symm,?_,?_⟩
    · intro s t he
      obtain ⟨j,hj,u,hju⟩ := (show b t∈walkCarrier F p from hb ▸ mem_range_self t)
      have hji : j≠i := by
        intro hji
        subst j
        exact hp'.2 ((edgeKey_eq F i x v).mpr hix ▸ hj)
      obtain ⟨r,hr⟩ := ha ▸ (mem_range_self s : a s∈range a)
      have hre := ((hF hji.symm).1 r u (hr.trans (he.trans hju.symm))).1
      have hav : a s=x.val ∨ a s=v.val := by
        rcases hre with rfl|rfl <;> rcases hix with hix|hix
        · exact Or.inl (hr.symm.trans hix.1)
        · exact Or.inr (hr.symm.trans hix.2)
        · exact Or.inr (hr.symm.trans hix.2)
        · exact Or.inl (hr.symm.trans hix.1)
      rcases hav with hx|hv
      · exact ⟨Or.inl (a.injective (hx.trans ha₀.symm)),Or.inl (b.injective (he.symm.trans (hx.trans hb₀.symm)))⟩
      · exact ⟨Or.inr (a.injective (hv.trans ha₁.symm)),Or.inr (b.injective (he.symm.trans (hv.trans hb₁.symm)))⟩
    · rw [ha,hb,walkCarrier_cons F hF h p hix]

theorem cycle_edges_isolated [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) {E : Set ι}
    (hG : (edgeGraph F E).IsCycles) {x : GraphVertices F}
    (p : (edgeGraph F E).Walk x x) (hp : p.IsCycle) :
    Disjoint (walkCarrier F p) (⋃ i∈{i∈E | edgeKey F i∉p.edges},range (F i)) := by
  apply disjoint_left.mpr
  intro z hz hzi
  obtain ⟨i,⟨hi,hip⟩,s,his⟩ := mem_iUnion₂.mp hzi
  obtain ⟨j,hjp,t,hjt⟩ := hz
  have hij : i≠j := by intro h; exact hip (h ▸ hjp)
  have hends := ((hF hij).1 s t (his.trans hjt.symm)).1
  have hv : Vertex F z := by
    refine ⟨i,?_⟩
    rcases hends with rfl|rfl
    · exact Or.inl his
    · exact Or.inr his
  let v : GraphVertices F := ⟨z,hv⟩
  have hvp : v∈p.support := walkCarrier_vertex F hF ⟨j,hjp,t,hjt⟩
  obtain ⟨w,hw⟩ := vertex_spans F hF hv ⟨s,his⟩
  let w' : GraphVertices F := ⟨w,hw.vertex_right⟩
  have hed : (edgeGraph F E).Adj v w' := ⟨i,hi,hw⟩
  have hk := cycle_saturated hG p hp hvp hed
  exact hip ((edgeKey_eq F i v w').mpr hw ▸ hk)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem pair_no_cut (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) (q : ℂ) :
    IsConnected ((range a∪range b)\{q}) := by
  refine ⟨?_,?_⟩
  · by_cases h : a 0=q
    · exact ⟨a 1,Or.inl (mem_range_self 1),fun he => a.endpoints_ne (h.trans he.symm)⟩
    · exact ⟨a 0,Or.inl (mem_range_self 0),h⟩
  · apply isPreconnected_of_forall_constant
    intro f hf x hx y hy
    have hends (hs : a 0≠q) (ht : a 1≠q) : f (a 0)=f (a 1) := by
      by_cases hqa : q∈range a
      · have hqb : q∉range b := by
          obtain ⟨s,hsq⟩ := hqa
          rintro ⟨t,htq⟩
          rcases (hc s t (hsq.trans htq.symm)).1 with rfl|rfl
          · exact hs hsq
          · exact ht hsq
        rw [h₀,h₁]
        apply arc_label_interval b hf zero_le_one
        intro t ht
        exact ⟨Or.inr (mem_range_self t),fun h => hqb ⟨t,h⟩⟩
      · apply arc_label_interval a hf zero_le_one
        intro t ht
        exact ⟨Or.inl (mem_range_self t),fun h => hqa ⟨t,h⟩⟩
    have endpoint {z : ℂ} (hz : z∈(range a∪range b)\{q}) :
        ∃ w,w∈({a 0,a 1} : Set ℂ) ∧ w≠q ∧ f z=f w := by
      rcases hz.1 with ⟨t,rfl⟩|⟨t,rfl⟩
      · obtain ⟨e,he,heq,hf⟩ := arc_punctured_endpoint_label a (S:=range a∪range b) subset_union_left hf hz.2
        refine ⟨a e,?_,heq,hf⟩
        rcases he with rfl|rfl <;> simp
      · obtain ⟨e,he,heq,hf⟩ := arc_punctured_endpoint_label b (S:=range a∪range b) subset_union_right hf hz.2
        refine ⟨b e,?_,heq,hf⟩
        rcases he with rfl|rfl
        · simp [←h₀]
        · simp [←h₁]
    obtain ⟨u,hu,huq,hxu⟩ := endpoint hx
    obtain ⟨v,hv,hvq,hyv⟩ := endpoint hy
    rw [hxu,hyv]
    rcases hu with rfl|hu <;> rcases hv with rfl|hv
    · rfl
    · rw [mem_singleton_iff] at hv
      subst v
      exact hends huq hvq
    · rw [mem_singleton_iff] at hu
      subst u
      exact (hends hvq huq).symm
    · exact congrArg f (hu.trans hv.symm)

theorem pair_component_local_access (a b : Arc ℂ) (h₀ : a 0=b 0) (h₁ : a 1=b 1)
    (hc : ∀ s t,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (P : Finset (ℂ × ℂ)) (ha : range a⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2)
    {q : ℂ} (hq : q∈range a∪range b) :
    ∃ r>0,∀ s : ℝ,0<s → s≤r → ∀ x : ℂ,
      IsPreconnected (connectedComponentIn (range a∪range b)ᶜ x∩ball q s) := by
  obtain ⟨A,hA⟩ := finite_graph_exact_segments (fun _ : Unit => a) P (fun _ => ha)
  obtain ⟨B,hB⟩ := finite_graph_exact_segments (fun _ : Unit => b) P (fun _ => hb)
  simp only [iUnion_const] at hA hB
  have he : range a∪range b=⋃ p∈A∪B,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hA,←hB]
  rw [he]
  exact noncut_locally_connected_faces (A∪B) (he ▸ hq) (he ▸ pair_no_cut a b h₀ h₁ hc q)
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
