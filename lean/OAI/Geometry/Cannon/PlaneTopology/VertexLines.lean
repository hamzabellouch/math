import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.HalfParam

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

namespace CannonEmbeddedArc.Arc
open Set unitInterval Metric Topology CannonPolygonal CannonSectors

variable {ι : Type*} [Finite ι]

theorem finite_prescribed_star_type {J : Type*} [Finite J] (P : Finset (ℂ × ℂ)) {a x : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (y : J → ℂ) (C : J → Set ℂ)
    (hy : ∀ i,y i∈⋃ p∈P,segment ℝ p.1 p.2)
    (hC : ∀ i,IsOpen (C i)) (hyC : ∀ i,y i∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → y i+t • (z-y i)∈C i) :
    ∃ G : J → Arc ℂ,
      Pairwise (fun i j => ∀ s t : I,G i s=G j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      (∀ i,G i 0=x) ∧ (∀ i,G i 1=y i) ∧ (∀ i,FiniteSupport (range (G i))) ∧
      (∀ i,G i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      ∀ i,∃ ε : ℝ,0<ε ∧ range (G i)∩ball (y i) ε⊆insert (y i) (C i) := by
  classical
  let _ := Fintype.ofFinite J
  let e := Fintype.equivFin J
  obtain ⟨G,hG,h₀,h₁,hS,hU,hgerm⟩ := finite_prescribed_star P hx (Fintype.card J)
    (fun i => y (e.symm i)) (fun i => C (e.symm i))
    (fun i => hy (e.symm i)) (fun i => hC (e.symm i)) (fun i => hyC (e.symm i))
    (fun i => hCU (e.symm i)) (fun i => hrad (e.symm i))
  refine ⟨fun i => G (e i),?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    exact hG (e.injective.ne hij)
  · exact fun i => h₀ (e i)
  · intro i
    simpa only [e.symm_apply_apply] using h₁ (e i)
  · exact fun i => hS (e i)
  · exact fun i => hU (e i)
  · intro i
    simpa only [e.symm_apply_apply] using hgerm (e i)

theorem graph_face_prescribed_fan {J : Type*} [Finite J]
    (F : ι → Arc ℂ) (P : Finset (ℂ × ℂ))
    (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) {a x : ℂ}
    (hx : x∈connectedComponentIn (⋃ i,range (F i))ᶜ a)
    (y : J → ℂ) (C : J → Set ℂ)
    (hy : ∀ i,y i∈⋃ j,range (F j))
    (hC : ∀ i,IsOpen (C i)) (hyC : ∀ i,y i∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ j,range (F j))ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → y i+t • (z-y i)∈C i) :
    ∃ G : J → Arc ℂ,
      Pairwise (fun i j => ∀ s t : I,G i s=G j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      (∀ i,G i 0=x) ∧ (∀ i,G i 1=y i) ∧ (∀ i,FiniteSupport (range (G i))) ∧
      (∀ i,G i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ j,range (F j))ᶜ a) ∧
      ∀ i,∃ ε : ℝ,0<ε ∧ range (G i)∩ball (y i) ε⊆insert (y i) (C i) := by
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  rw [hQ] at hx hy hCU ⊢
  exact finite_prescribed_star_type Q hx y C hy hC hyC hCU hrad

structure VertexLines (F : ι → Arc ℂ) (x : ℂ) where
  linear : {i // x∈range (F i)} → (ℂ →L[ℝ] ℝ)
  surjective : ∀ i,Function.Surjective (linear i)
  radius : ℝ
  positive : 0<radius
  cover : ∀ z∈(⋃ i,range (F i))∩ball x radius,∃ i,linear i (z-x)=0

theorem vertexLines_nonempty (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {x : ℂ} (hx : Vertex F x) : Nonempty (VertexLines F x) := by
  obtain ⟨L,hL,r,hr,hcover⟩ := tame_vertex_lines F hF P hP hx
  exact ⟨⟨L,hL,r,hr,hcover⟩⟩

def FaceGerm (F : ι → Arc ℂ) (V : Finset ℂ) (D : ∀ v : V,VertexLines F v.val) (U : Set ℂ) :=
  Σ v : V,{b : {i // v.val∈range (F i)} → Bool //
    (sector (D v).linear v.val (D v).radius b).Nonempty ∧
      sector (D v).linear v.val (D v).radius b⊆U}

instance faceGerm_finite (F : ι → Arc ℂ) (V : Finset ℂ)
    (D : ∀ v : V,VertexLines F v.val) (U : Set ℂ) : Finite (FaceGerm F V D U) := by
  unfold FaceGerm
  infer_instance

def FaceGerm.point {F : ι → Arc ℂ} {V : Finset ℂ} {D : ∀ v : V,VertexLines F v.val}
    {U : Set ℂ} (g : FaceGerm F V D U) : ℂ := g.1.val

def FaceGerm.cone {F : ι → Arc ℂ} {V : Finset ℂ} {D : ∀ v : V,VertexLines F v.val}
    {U : Set ℂ} (g : FaceGerm F V D U) : Set ℂ := sector (D g.1).linear g.point (D g.1).radius g.2.val

lemma faceGerm_card (F : ι → Arc ℂ) (V : Finset ℂ)
    (D : ∀ v : V,VertexLines F v.val) (U : Set ℂ) {N : ℕ}
    (hN : ∀ v : V,Nat.card {i // v.val∈range (F i)}≤N) :
    Nat.card (FaceGerm F V D U)≤V.card*2^N := by
  classical
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite (FaceGerm F V D U)
  change Nat.card (Σ v : V,{b : {i // v.val∈range (F i)} → Bool //
    (sector (D v).linear v.val (D v).radius b).Nonempty ∧
      sector (D v).linear v.val (D v).radius b⊆U})≤_
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
  calc
    _≤∑ v : V,2^N := by
      apply Finset.sum_le_sum
      intro v _
      calc
        _≤Fintype.card ({i // v.val∈range (F i)} → Bool) := Fintype.card_subtype_le _
        _=2^(Nat.card {i // v.val∈range (F i)}) := by simp [Nat.card_eq_fintype_card]
        _≤2^N := Nat.pow_le_pow_right (by omega) (hN v)
    _=V.card*2^N := by simp

lemma faceGerm_at_vertex (F : ι → Arc ℂ) (V : Finset ℂ)
    (D : ∀ v : V,VertexLines F v.val) {a : ℂ} (v : V)
    (hv : v.val∈closure (connectedComponentIn (⋃ i,range (F i))ᶜ a)) :
    ∃ g : FaceGerm F V D (connectedComponentIn (⋃ i,range (F i))ᶜ a),g.point=v.val := by
  obtain ⟨b,hb,hsub,_⟩ := face_contains_sector
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed)
    (D v).linear (D v).surjective (D v).positive (D v).cover hv
  exact ⟨⟨v,b,hb,hsub⟩,rfl⟩

theorem face_all_sector_fan (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {a x : ℂ} (hx : x∈connectedComponentIn (⋃ i,range (F i))ᶜ a)
    (V : Finset ℂ) (hV : ∀ v∈V,Vertex F v)
    (hcl : ∀ v∈V,v∈closure (connectedComponentIn (⋃ i,range (F i))ᶜ a))
    {N : ℕ} (hN : ∀ v : V,Nat.card {i // v.val∈range (F i)}≤N) :
    ∃ D : ∀ v : V,VertexLines F v.val,
      ∃ G : FaceGerm F V D (connectedComponentIn (⋃ i,range (F i))ᶜ a) → Arc ℂ,
      Nat.card (FaceGerm F V D (connectedComponentIn (⋃ i,range (F i))ᶜ a))≤V.card*2^N ∧
      (∀ v : V,∃ g,G g 1=v.val) ∧
      Pairwise (fun i j => ∀ s t : I,G i s=G j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      (∀ i,G i 0=x) ∧ (∀ i,G i 1=i.point) ∧ (∀ i,FiniteSupport (range (G i))) ∧
      (∀ i,G i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ j,range (F j))ᶜ a) ∧
      ∀ i,∃ ε : ℝ,0<ε ∧ range (G i)∩ball i.point ε⊆insert i.point i.cone := by
  classical
  let D : ∀ v : V,VertexLines F v.val := fun v =>
    Classical.choice (vertexLines_nonempty F hF P hP (hV v.val v.property))
  let U := connectedComponentIn (⋃ i,range (F i))ᶜ a
  let J := FaceGerm F V D U
  have hpoint (g : J) : g.point∈⋃ i,range (F i) := by
    obtain ⟨i,hi⟩ := hV g.1.val g.1.property
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    rcases hi with hi|hi
    · exact ⟨0,hi⟩
    · exact ⟨1,hi⟩
  obtain ⟨G,hG,h₀,h₁,hS,hGU,hgerm⟩ := graph_face_prescribed_fan F P hP hx
    (fun g : J => g.point) (fun g => g.cone) hpoint
    (fun g => sector_open (D g.1).linear g.point (D g.1).radius g.2.val) (fun g => sector_vertex_closure _ _ _ _ g.2.property.1)
    (fun g => g.2.property.2) (fun g _ hz _ ht ht₁ => sector_radial _ _ _ _ hz ht ht₁)
  refine ⟨D,G,faceGerm_card F V D U hN,?_,hG,h₀,h₁,hS,hGU,hgerm⟩
  intro v
  obtain ⟨g,hg⟩ := faceGerm_at_vertex F V D v (hcl v.val v.property)
  exact ⟨g,(h₁ g).trans hg⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Finite ι]

omit [Finite ι] in
lemma vertex_mem_support (F : ι → Arc ℂ) {v : ℂ} (hv : Vertex F v) :
    v∈⋃ i,range (F i) := by
  obtain ⟨i,hi⟩ := hv
  exact mem_iUnion.mpr ⟨i,hi.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)⟩

omit [Finite ι] in
lemma vertex_parameter (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι) {t : I}
    (ht : Vertex F (F i t)) : t=0 ∨ t=1 := by
  by_contra hn
  push Not at hn
  exact interior_not_vertex F hF i (lt_of_le_of_ne (nonneg t) hn.1.symm)
    (lt_of_le_of_ne (le_one t) hn.2) ht

def Faces (F : ι → Arc ℂ) := ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)
def face (F : ι → Arc ℂ) (d : Faces F) : Set ℂ :=
  region _ ConnectedComponents.mk d
noncomputable def faceVertices (F : ι → Arc ℂ) (d : Faces F) : Finset ℂ :=
  ((finite_vertex_set F).inter_of_left (s:={x | Vertex F x}) (t:=closure (face F d))).toFinset

lemma mem_faceVertices (F : ι → Arc ℂ) (d : Faces F) (v : ℂ) :
    v∈faceVertices F d ↔ Vertex F v ∧ v∈closure (face F d) := by
  simp [faceVertices]

omit [Finite ι] in
lemma face_nonempty (F : ι → Arc ℂ) (d : Faces F) : (face F d).Nonempty :=
  (component_region_connected _ d).nonempty
lemma face_open (F : ι → Arc ℂ) (d : Faces F) : IsOpen (face F d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  exact region_isOpen (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl
    ConnectedComponents.continuous_coe d

lemma faces_finite [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) :
    Finite (Faces F) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨f,hf⟩ := tame_face_labels_surjection F hF P hP
    ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  exact Finite.of_surjective f hf

theorem face_vertex_fan (F : ι → Arc ℂ) (P : Finset (ℂ × ℂ))
    (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces F) {x : ℂ} (hx : x∈face F d) :
    ∃ A : faceVertices F d → Arc ℂ,
      Pairwise (fun u v => Compatible (A u) (A v)) ∧
      (∀ v,A v 0=x) ∧ (∀ v,A v 1=v.val) ∧
      (∀ v,FiniteSupport (range (A v))) ∧
      (∀ v,A v '' Ioo (0:I) 1⊆face F d) := by
  obtain ⟨Q,hQ⟩ := finite_graph_exact_segments F P hP
  obtain ⟨a,ha⟩ := ConnectedComponents.surjective_coe d
  have hface : face F d=connectedComponentIn (⋃ p∈Q,segment ℝ p.1 p.2)ᶜ a.val := by
    unfold face
    rw [←ha,component_region_eq]
    exact congrArg (fun K : Set ℂ => connectedComponentIn Kᶜ a.val) hQ
  obtain ⟨A,hA,h₀,h₁,hS,hU⟩ := finite_tame_star Q
    (hQ ▸ (show a.val∉⋃ i,range (F i) from a.property)) (hface ▸ hx) (faceVertices F d) (by
      intro v hv
      obtain ⟨hv,hcl⟩ := (mem_faceVertices F d v).mp hv
      exact ⟨hQ ▸ vertex_mem_support F hv,hface ▸ hcl⟩)
  exact ⟨A,hA,h₀,h₁,hS,fun v => by simpa only [←hface] using hU v⟩

omit [Finite ι] in
lemma fan_parameter_in_face {F : ι → Arc ℂ} {d : Faces F} {a : Arc ℂ}
    (h₀ : a 0∈face F d) (hU : a '' Ioo (0:I) 1⊆face F d) {t : I} (ht : t≠1) :
    a t∈face F d := by
  by_cases h : t=0
  · simpa only [h] using h₀
  · exact hU ⟨t,⟨lt_of_le_of_ne (nonneg t) (Ne.symm h),lt_of_le_of_ne (le_one t) ht⟩,rfl⟩

omit [Finite ι] in
lemma old_fan_compatible (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (i : ι)
    {d : Faces F} {a : Arc ℂ} (h₀ : a 0∈face F d)
    (h₁ : Vertex F (a 1)) (hU : a '' Ioo (0:I) 1⊆face F d) : Compatible (F i) a := by
  have hend {s t : I} (h : F i s=a t) : t=1 := by
    by_contra ht
    exact (fan_parameter_in_face h₀ hU ht).1 (mem_iUnion.mpr ⟨i,s,h⟩)
  constructor
  · intro s t h
    have ht := hend h
    refine ⟨vertex_parameter F hF i ?_,Or.inr ht⟩
    simpa only [h,ht] using h₁
  · rintro z ⟨⟨s,rfl⟩,⟨t,ht⟩⟩ w ⟨⟨u,rfl⟩,⟨v,hv⟩⟩
    rw [←ht,←hv,hend ht.symm,hend hv.symm]

omit [Finite ι] in
lemma different_face_fans_compatible {F : ι → Arc ℂ} {d e : Faces F} (hde : d≠e)
    {a b : Arc ℂ} (ha₀ : a 0∈face F d) (hb₀ : b 0∈face F e)
    (ha₁ : a 1∈⋃ i,range (F i)) (hb₁ : b 1∈⋃ i,range (F i))
    (haU : a '' Ioo (0:I) 1⊆face F d) (hbU : b '' Ioo (0:I) 1⊆face F e) :
    Compatible a b := by
  have hend {s t : I} (h : a s=b t) : s=1 ∧ t=1 := by
    by_cases hs : s=1
    · refine ⟨hs,?_⟩
      by_contra ht
      exact (fan_parameter_in_face hb₀ hbU ht).1 (by simpa only [←h,hs] using ha₁)
    · have has := fan_parameter_in_face ha₀ haU hs
      by_cases ht : t=1
      · exact (has.1 (by simpa only [h,ht] using hb₁)).elim
      · have hbt := fan_parameter_in_face hb₀ hbU ht
        exact (hde (has.2.symm.trans (by simpa only [h] using hbt.2))).elim
  constructor
  · intro s t h
    exact ⟨Or.inr (hend h).1,Or.inr (hend h).2⟩
  · rintro z ⟨⟨s,rfl⟩,⟨t,ht⟩⟩ w ⟨⟨u,rfl⟩,⟨v,hv⟩⟩
    rw [(hend ht.symm).1,(hend hv.symm).1]

theorem global_vertex_stellation (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) :
    ∃ (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ),
      (∀ d,c d∈face F d) ∧
      Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)) ∧
      (∀ i,A i 0=c i.1) ∧ (∀ i,A i 1=i.2.val) ∧
      (∀ i,FiniteSupport (range (A i))) ∧
      (∀ i,A i '' Ioo (0:I) 1⊆face F i.1) := by
  classical
  choose c hc using face_nonempty F
  choose A hA h₀ h₁ hS hU using fun d => face_vertex_fan F P hP d (hc d)
  refine ⟨c,(fun i => A i.1 i.2),hc,?_,(fun i => h₀ i.1 i.2),
    (fun i => h₁ i.1 i.2),(fun i => hS i.1 i.2),(fun i => hU i.1 i.2)⟩
  intro i j hij
  rcases i with i|⟨d,v⟩ <;> rcases j with j|⟨e,w⟩
  · exact hF (fun h => hij (congrArg Sum.inl h))
  · exact old_fan_compatible F hF i (h₀ e w ▸ hc e)
      (h₁ e w ▸ ((mem_faceVertices F e w.val).mp w.property).1) (hU e w)
  · exact (old_fan_compatible F hF j (h₀ d v ▸ hc d)
      (h₁ d v ▸ ((mem_faceVertices F d v.val).mp v.property).1) (hU d v)).symm
  · by_cases hde : d=e
    · subst e
      exact hA d (fun he => hij (by cases he; rfl))
    · exact different_face_fans_compatible hde (h₀ d v ▸ hc d) (h₀ e w ▸ hc e)
        (h₁ d v ▸ vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1)
        (h₁ e w ▸ vertex_mem_support F ((mem_faceVertices F e w.val).mp w.property).1)
        (hU d v) (hU e w)
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

end OAI
