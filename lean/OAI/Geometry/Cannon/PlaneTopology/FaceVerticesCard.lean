import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.PairComponentClosure

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
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Finite ι]

theorem face_vertices_card_le (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) (d : Faces F) :
    Nat.card (faceVertices F d)≤2*Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let K := ⋃ i,range (F i)
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let E := regionEdges F ConnectedComponents.mk d
  have hend (i : E) (b : Bool) : (if b then F i.val 1 else F i.val 0)∈faceVertices F d := by
    apply (mem_faceVertices F d _).mpr
    have hh := region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe i.property
    cases b
    · exact ⟨⟨i.val,Or.inl rfl⟩,hh (mem_range_self 0)⟩
    · exact ⟨⟨i.val,Or.inr rfl⟩,hh (mem_range_self 1)⟩
  let f : E × Bool → faceVertices F d := fun p => ⟨_,hend p.1 p.2⟩
  have hsur : Function.Surjective f := by
    intro v
    obtain ⟨hv,hvcl⟩ := (mem_faceVertices F d v.val).mp v.property
    have hK := vertex_mem_support F hv
    have hcl : closure (face F d)=face F d∪⋃ i∈E,range (F i) := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
    rw [hcl] at hvcl
    have hh := hvcl.resolve_left (fun h => h.1 hK)
    obtain ⟨i,hi,t,ht⟩ := mem_iUnion₂.mp hh
    have ht' := vertex_parameter F hF i (ht ▸ hv)
    rcases ht' with rfl|rfl
    · exact ⟨(⟨i,hi⟩,false),Subtype.ext ht⟩
    · exact ⟨(⟨i,hi⟩,true),Subtype.ext ht⟩
  have hh := Nat.card_le_card_of_surjective f hsur
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool,mul_comm] using hh

lemma stellar_old_edge_parent (F : ι → Arc ℂ)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d)
    {i : ι} (hi : Sum.inl i∈regionEdges (Sum.elim F A) ConnectedComponents.mk e) :
    i∈regionEdges F ConnectedComponents.mk d := by
  obtain ⟨t,ht₀,ht₁,ht⟩ := hi
  exact ⟨t,ht₀,ht₁,closure_mono hsub ht⟩

theorem stellar_face_edges_card_le (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (hG : Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {d : Faces F} {e : Faces (Sum.elim F A)} (hsub : face (Sum.elim F A) e⊆face F d) :
    Nat.card (regionEdges (Sum.elim F A) ConnectedComponents.mk e)≤
      3*Nat.card (regionEdges F ConnectedComponents.mk d) := by
  classical
  let E := regionEdges F ConnectedComponents.mk d
  let E' := regionEdges (Sum.elim F A) ConnectedComponents.mk e
  let g : E ⊕ (faceVertices F d) → ι ⊕ (Σ d : Faces F,faceVertices F d) :=
    Sum.elim (fun i => Sum.inl i.val) (fun v => Sum.inr ⟨d,v⟩)
  have hsub' : E'⊆range g := by
    rintro (i|⟨d',v⟩) hi
    · exact ⟨Sum.inl ⟨i,stellar_old_edge_parent F A hsub hi⟩,rfl⟩
    · have hd : d'=d := stellar_spoke_parent F c A hc h₀ hU hG Q hQ hsub hi
      subst d'
      exact ⟨Sum.inr v,rfl⟩
  have h1 := Nat.card_mono (toFinite (range g)) hsub'
  have h2 : Nat.card (range g)≤Nat.card (E⊕(faceVertices F d)) :=
    Nat.card_le_card_of_surjective (fun x => (⟨g x,mem_range_self x⟩ : range g)) (by
      rintro ⟨y,⟨x,rfl⟩⟩; exact ⟨x,rfl⟩)
  have hv := face_vertices_card_le F hF P hP d
  rw [Nat.card_sum] at h2
  change Nat.card E'≤3*Nat.card E
  change Nat.card (faceVertices F d)≤2*Nat.card E at hv
  omega
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι X : Type*} [Finite ι] [Nonempty ι] [PseudoMetricSpace X]

omit [Nonempty ι] in
lemma stellar_spoke_closure (F : ι → Arc ℂ)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (i : Σ d : Faces F,faceVertices F d) : range (A i)⊆closure (face F i.1) := by
  rintro z ⟨t,rfl⟩
  by_cases ht₀ : t=0
  · rw [ht₀,h₀]; exact subset_closure (hc i.1)
  by_cases ht₁ : t=1
  · rw [ht₁,h₁]; exact ((mem_faceVertices F i.1 i.2.val).mp i.2.property).2
  exact subset_closure (hU i ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm ht₀),
    lt_of_le_of_ne (le_one t) ht₁⟩,rfl⟩)

theorem near_faces_card_le (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (f : ℂ → X) (D : ℝ)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (x : X) (R : ℝ) :
    Nat.card {d : Faces F | ∃ z∈closure (face F d),dist (f z) x<R}≤
      2*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+D} := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  choose labels hlabels using tame_edge_incident_labels F hF P hP ConnectedComponents.continuous_coe
  let H := {d : Faces F | ∃ z∈closure (face F d),dist (f z) x<R}
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R+D}
  let g : E × Bool → Faces F := fun p => labels p.1.val p.2
  have hsub : H⊆range g := by
    rintro d ⟨z,hz,hzx⟩
    obtain ⟨i,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge F hF ConnectedComponents.continuous_coe d (face_nonempty F d)
    have hi : i∈E := by
      refine ⟨t,?_⟩
      have hd := hdiam d (F i t) ht z hz
      have hh := dist_triangle (f (F i t)) (f z) x
      linarith
    have ht' : d∈range (labels i) := by rw [←hlabels i t ht₀ ht₁]; exact ht
    obtain ⟨b,hb⟩ := ht'
    exact ⟨(⟨i,hi⟩,b),hb⟩
  have h1 := Nat.card_mono (toFinite (range g)) hsub
  have h2 : Nat.card (range g)≤Nat.card (E × Bool) :=
    Nat.card_le_card_of_surjective (fun a => (⟨g a,mem_range_self a⟩ : range g)) (by
      rintro ⟨y,⟨a,rfl⟩⟩; exact ⟨a,rfl⟩)
  have hh := h1.trans h2
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool,mul_comm] using hh

theorem stellar_spokes_local_card (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (B : ℕ) (hB : ∀ d,Nat.card (regionEdges F ConnectedComponents.mk d)≤B)
    (f : ℂ → X) (D : ℝ)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (x : X) (R : ℝ) :
    Nat.card {i : Σ d : Faces F,faceVertices F d | ∃ t:I,dist (f (A i t)) x<R}≤
      4*B*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+D} := by
  classical
  let H := {d : Faces F | ∃ z∈closure (face F d),dist (f z) x<R}
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R+D}
  let S := {i : Σ d : Faces F,faceVertices F d | ∃ t:I,dist (f (A i t)) x<R}
  have hparent (i : S) : i.val.1∈H := by
    obtain ⟨t,ht⟩ := i.property
    exact ⟨A i.val t,stellar_spoke_closure F c A hc h₀ h₁ hU i.val (mem_range_self t),ht⟩
  let g : S → (Σ d : H,faceVertices F d.val) := fun i => ⟨⟨i.val.1,hparent i⟩,i.val.2⟩
  have hg : Function.Injective g := by
    intro i j he
    apply Subtype.ext
    exact congrArg (fun a : Σ d : H,faceVertices F d.val => (⟨a.1.val,a.2⟩ : Σ d : Faces F,faceVertices F d)) he
  let _ : Fintype H := Fintype.ofFinite H
  have hcount : Nat.card (Σ d : H,faceVertices F d.val)≤Nat.card H*(2*B) := by
    rw [Nat.card_sigma]
    calc
      _≤∑ _d : H,2*B := Finset.sum_le_sum (fun d _ =>
        (face_vertices_card_le F hF P hP d.val).trans (Nat.mul_le_mul_left 2 (hB d.val)))
      _=Nat.card H*(2*B) := by simp [Nat.card_eq_fintype_card]
  have hf := near_faces_card_le F hF P hP f D hdiam x R
  change Nat.card H≤2*Nat.card E at hf
  have hh := (Nat.card_le_card_of_injective g hg).trans hcount
  change Nat.card S≤4*B*Nat.card E
  exact hh.trans (by nlinarith)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

variable {ι X : Type*} [Finite ι] [Nonempty ι] [PseudoMetricSpace X]

theorem stellar_graph_local_card (F : ι → Arc ℂ) [Finite (Faces F)]
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hc : ∀ d,c d∈face F d) (h₀ : ∀ i,A i 0=c i.1)
    (h₁ : ∀ i,A i 1=i.2.val) (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    (B : ℕ) (hB : ∀ d,Nat.card (regionEdges F ConnectedComponents.mk d)≤B)
    (f : ℂ → X) (D : ℝ) (hD : 0≤D)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (x : X) (R : ℝ) :
    Nat.card {i : ι ⊕ (Σ d : Faces F,faceVertices F d) | ∃ t:I,dist (f (Sum.elim F A i t)) x<R}≤
      (1+4*B)*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+D} := by
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R+D}
  have hOld : Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R}≤Nat.card E := by
    apply Nat.card_mono (toFinite E)
    rintro i ⟨t,ht⟩
    exact ⟨t,lt_of_lt_of_le ht (le_add_of_nonneg_right hD)⟩
  have hNew := stellar_spokes_local_card F hF P hP c A hc h₀ h₁ hU B hB f D hdiam x R
  have he : Nat.card {i : ι ⊕ (Σ d : Faces F,faceVertices F d) | ∃ t:I,dist (f (Sum.elim F A i t)) x<R}=
      Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R}+
      Nat.card {i : Σ d : Faces F,faceVertices F d | ∃ t:I,dist (f (A i t)) x<R} :=
    (Nat.card_congr Equiv.subtypeSum).trans Nat.card_sum
  rw [he]
  change _≤(1+4*B)*Nat.card E
  change _≤4*B*Nat.card E at hNew
  nlinarith

omit [Nonempty ι] in
theorem vertices_local_card (F : ι → Arc ℂ) (f : ℂ → X) (x : X) (R : ℝ) :
    Nat.card {z : ℂ | Vertex F z ∧ dist (f z) x<R}≤
      2*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R} := by
  classical
  let E := {i : ι | ∃ t:I,dist (f (F i t)) x<R}
  let g : E × Bool → ℂ := fun p => if p.2 then F p.1.val 1 else F p.1.val 0
  have hsub : {z : ℂ | Vertex F z ∧ dist (f z) x<R}⊆range g := by
    rintro z ⟨⟨i,hiz⟩,hz⟩
    rcases hiz with hiz|hiz
    · refine ⟨(⟨i,⟨0,by simpa only [hiz] using hz⟩⟩,false),?_⟩
      exact hiz
    · refine ⟨(⟨i,⟨1,by simpa only [hiz] using hz⟩⟩,true),?_⟩
      exact hiz
  have h1 := Nat.card_mono (toFinite (range g)) hsub
  have h2 : Nat.card (range g)≤Nat.card (E × Bool) :=
    Nat.card_le_card_of_surjective (fun a => (⟨g a,mem_range_self a⟩ : range g)) (by
      rintro ⟨y,⟨a,rfl⟩⟩; exact ⟨a,rfl⟩)
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_bool,mul_comm] using h1.trans h2
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonFaceIncidence CannonPolygonal

universe u
variable {ι : Type u} [Finite ι] [Nonempty ι]
variable {X : Type*} [PseudoMetricSpace X]

omit [Nonempty ι] in
lemma support_subset_stellar (F : ι → Arc ℂ)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ) :
    (⋃ i,range (F i))⊆⋃ i,range (Sum.elim F A i : Arc ℂ) := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨Sum.inl i,hi⟩

omit [Nonempty ι] in
lemma stellar_support_finite (F : ι → Arc ℂ) [Finite (Faces F)]
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hA : ∀ i,FiniteSupport (range (A i))) :
    ∃ Q : Finset (ℂ × ℂ),∀ i,range (Sum.elim F A i : Arc ℂ)⊆⋃ p∈Q,segment ℝ p.1 p.2 := by
  have hS : ∀ i,FiniteSupport (range (Sum.elim F A i : Arc ℂ)) := by
    rintro (i|i)
    · exact ⟨P,hP i⟩
    · exact hA i
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hS
  exact ⟨Q,fun i => (subset_iUnion _ i).trans hQ⟩

omit [Nonempty ι] in
lemma stellar_faces_diam (F : ι → Arc ℂ) [Finite (Faces F)]
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ) (f : ℂ → X) (D : ℝ)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D) :
    ∀ e,∀ z∈closure (face (Sum.elim F A) e),∀ w∈closure (face (Sum.elim F A) e),dist (f z) (f w)≤D := by
  intro e z hz w hw
  obtain ⟨d,hd⟩ := face_parent F (Sum.elim F A) (support_subset_stellar F A) e
  exact hdiam d z (closure_mono hd hz) w (closure_mono hd hw)

theorem quantitative_triangular_refinement (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hconn : IsPreconnected (⋃ i,range (F i)))
    (f : ℂ → X) (D E : ℝ) (hD : 0≤D)
    (hdiam : ∀ d,∀ z∈closure (face F d),∀ w∈closure (face F d),dist (f z) (f w)≤D)
    (hEdge : ∀ i,∀ t s : I,dist (f (F i t)) (f (F i s))≤E)
    (B : ℕ) (hB : ∀ d,Nat.card (regionEdges F ConnectedComponents.mk d)≤B) :
    ∃ (κ : Type u) (H : κ → Arc ℂ), Finite κ ∧ Nonempty κ ∧
      Pairwise (fun i j => Compatible (H i) (H j)) ∧
      (∃ Q : Finset (ℂ × ℂ),∀ i,range (H i)⊆⋃ p∈Q,segment ℝ p.1 p.2) ∧
      (⋃ i,range (F i))⊆(⋃ i,range (H i)) ∧
      (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
      (∀ i,∀ t s : I,dist (f (H i t)) (f (H i s))≤ max E D) ∧
      (∀ e,∀ z∈closure (face H e),∀ w∈closure (face H e),dist (f z) (f w)≤D) ∧
      (∀ x : X,∀ R : ℝ,
        Nat.card {i : κ | ∃ t:I,dist (f (H i t)) x<R}≤
          (1+12*B)*(1+4*B)*Nat.card {i : ι | ∃ t:I,dist (f (F i t)) x<R+2*D}) ∧
      (∀ e : Faces H,∃ i j k : κ,i≠j ∧ j≠k ∧ k≠i ∧
        frontier (face H e)=range (H i)∪range (H j)∪range (H k) ∧
        closure (face H e)=face H e∪(range (H i)∪range (H j)∪range (H k))) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF P hP
  obtain ⟨c,A,hc,hG,h₀,h₁,hS,hU,hGK⟩ := global_stellation_no_cut_points F hF P hP hconn
  let G := Sum.elim F A
  obtain ⟨Q,hQ⟩ := stellar_support_finite F P hP A hS
  have hGK' : ∀ q : ℂ,IsPreconnected ((⋃ i,range (G i))\{q}) := by
    intro q
    simpa only [G,iUnion_sum,Sum.elim_inl,Sum.elim_inr] using hGK q
  have hGdiam := stellar_faces_diam F A f D hdiam
  have hGB : ∀ d,Nat.card (regionEdges G ConnectedComponents.mk d)≤3*B := by
    intro e
    obtain ⟨d,hd⟩ := face_parent F G (support_subset_stellar F A) e
    exact (stellar_face_edges_card_le F hF P hP c A hc h₀ hU hG Q hQ hd).trans
      (Nat.mul_le_mul_left 3 (hB d))
  have hGE : ∀ i,∀ t s : I,dist (f (G i t)) (f (G i s))≤ max E D := by
    rintro (i|i) t s
    · exact (hEdge i t s).trans (le_max_left _ _)
    · exact (hdiam i.1 _ (stellar_spoke_closure F c A hc h₀ h₁ hU i (mem_range_self t))
        _ (stellar_spoke_closure F c A hc h₀ h₁ hU i (mem_range_self s))).trans (le_max_right _ _)
  let _ : Finite (Faces G) := faces_finite G hG Q hQ
  obtain ⟨c',A',hc',hH,h₀',h₁',hS',hU',hHK,hTri⟩ := global_triangular_stellation G hG Q hQ hGK'
  let H := Sum.elim G A'
  obtain ⟨Q',hQ'⟩ := stellar_support_finite G Q hQ A' hS'
  refine ⟨_,H,inferInstance,inferInstance,hH,⟨Q',hQ'⟩,
    (support_subset_stellar F A).trans (support_subset_stellar G A'),hHK,?_,
    stellar_faces_diam G A' f D hGdiam,?_,?_⟩
  · rintro (i|i) t s
    · exact hGE i t s
    · exact (hGdiam i.1 _ (stellar_spoke_closure G c' A' hc' h₀' h₁' hU' i (mem_range_self t))
        _ (stellar_spoke_closure G c' A' hc' h₀' h₁' hU' i (mem_range_self s))).trans (le_max_right _ _)
  · intro x R
    have h1 := stellar_graph_local_card G hG Q hQ c' A' hc' h₀' h₁' hU' (3*B) hGB f D hD hGdiam x R
    have h2 := stellar_graph_local_card F hF P hP c A hc h₀ h₁ hU B hB f D hD hdiam x (R+D)
    have hh := h1.trans (Nat.mul_le_mul_left (1+4*(3*B)) h2)
    have heR : R+D+D=R+2*D := by ring
    rw [heR] at hh
    have heB : 1+4*(3*B)=1+12*B := by omega
    rw [heB] at hh
    simpa only [Nat.mul_assoc] using hh
  · intro e
    obtain ⟨d,i,v,w,hiv,hiw,hvw,hsub,hfront,hcl⟩ := hTri e
    refine ⟨Sum.inl i,Sum.inr ⟨d,v⟩,Sum.inr ⟨d,w⟩,by simp,?_,by simp,hfront,hcl⟩
    intro he
    have hh := Sum.inr.inj he
    apply hvw
    apply Subtype.ext
    exact congrArg (fun a : Σ d : Faces G,faceVertices G d => a.2.val) hh
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric

variable {X : Type*} [PseudoMetricSpace X]
lemma continuous_closure_diam (f : ℂ → X) (hf : Continuous f) (U : Set ℂ) (D : ℝ)
    (h : ∀ z∈U,∀ w∈U,dist (f z) (f w)≤D) :
    ∀ z∈closure U,∀ w∈closure U,dist (f z) (f w)≤D := by
  have hrow (z : ℂ) (hz : z∈U) : closure U⊆{w | dist (f z) (f w)≤D} :=
    closure_minimal (h z hz) (isClosed_le (continuous_const.dist hf) continuous_const)
  intro z hz w hw
  have hcol : closure U⊆{z | dist (f z) (f w)≤D} :=
    closure_minimal (fun z hz => hrow z hz hw) (isClosed_le (hf.dist continuous_const) continuous_const)
  exact hcol hz
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
