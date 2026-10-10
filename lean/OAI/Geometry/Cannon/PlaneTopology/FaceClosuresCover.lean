import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.RegionEdges
import OAI.Geometry.Cannon.PlaneTopology.VertexLines
import OAI.Geometry.Cannon.Topology.LabelsConstant

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
open Set unitInterval Topology CannonPolygonal CannonFaceIncidence CannonSegmentCones

variable {ι : Type*}

lemma face_closures_cover [Finite ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2) :
    (⋃ d : Faces F,closure (face F d))=univ := by
  let _ : Finite (Faces F) := faces_finite F hF P hP
  have hd : Dense ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (complex_finite_segments_compl_dense P).mono (compl_subset_compl.mpr (iUnion_subset hP))
  have hh : closure ((⋃ i,range (F i))ᶜ : Set ℂ)⊆⋃ d : Faces F,closure (face F d) := by
    apply closure_minimal _ (isClosed_iUnion_of_finite fun _ => isClosed_closure)
    intro x hx
    exact mem_iUnion.mpr ⟨ConnectedComponents.mk ⟨x,hx⟩,subset_closure ⟨hx,rfl⟩⟩
  rw [hd.closure_eq] at hh
  exact eq_univ_of_univ_subset hh

lemma face_boundary_edges [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces F) {z : ℂ} (hz : z∈closure (face F d)) (hzK : z∈⋃ i,range (F i)) :
    ∃ i,z∈range (F i) ∧ range (F i)⊆closure (face F d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  have hh := tame_region_closure F hF P hP ConnectedComponents.continuous_coe d
  change z∈closure (region _ ConnectedComponents.mk d) at hz
  rw [hh] at hz
  rcases hz with hz|hz
  · exact (hz.1 hzK).elim
  · obtain ⟨i,hi,hiz⟩ := mem_iUnion₂.mp hz
    exact ⟨i,hiz,region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe hi⟩

lemma faceVertices_nontrivial [Finite ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (d : Faces F) : (faceVertices F d : Set ℂ).Nontrivial := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  obtain ⟨i,t,ht₀,ht₁,ht⟩ := tame_face_hits_edge F hF ConnectedComponents.continuous_coe d (face_nonempty F d)
  have hcl := region_edge_in_closure F hF P hP ConnectedComponents.continuous_coe ⟨t,ht₀,ht₁,ht⟩
  exact ⟨F i 0,(mem_faceVertices F d _).mpr ⟨⟨i,Or.inl rfl⟩,hcl (mem_range_self 0)⟩,
    F i 1,(mem_faceVertices F d _).mpr ⟨⟨i,Or.inr rfl⟩,hcl (mem_range_self 1)⟩,(F i).endpoints_ne⟩

lemma arc_label_interval {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} {f : X → Bool} (hf : ContinuousOn f S) {u v : I}
    (huv : u≤v) (hS : ∀ t∈Icc u v,a t∈S) : f (a u)=f (a v) := by
  exact isPreconnected_Icc.constant (hf.comp a.continuous.continuousOn hS)
    (left_mem_Icc.mpr huv) (right_mem_Icc.mpr huv)

lemma arc_punctured_endpoint_label {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} (hS : range a⊆S) {q : X} {f : X → Bool} (hf : ContinuousOn f (S\{q}))
    {t : I} (ht : a t≠q) :
    ∃ e : I,(e=0 ∨ e=1) ∧ a e≠q ∧ f (a t)=f (a e) := by
  classical
  by_cases h : ∀ s∈Icc (0:I) t,a s≠q
  · exact ⟨0,Or.inl rfl,h _ ⟨le_rfl,nonneg t⟩,
      (arc_label_interval a hf (nonneg t) (fun s hs => ⟨hS (mem_range_self s),h s hs⟩)).symm⟩
  · push Not at h
    obtain ⟨s,hs,hsq⟩ := h
    have hst : s<t := lt_of_le_of_ne hs.2 (fun he => ht (he ▸ hsq))
    have hn : ∀ u∈Icc t (1:I),a u≠q := by
      intro u hu he
      have hus := a.injective (he.trans hsq.symm)
      exact (not_lt_of_ge hu.1) (hus.symm ▸ hst)
    exact ⟨1,Or.inr rfl,hn _ ⟨le_one t,le_rfl⟩,
      arc_label_interval a hf (le_one t) (fun s hs => ⟨hS (mem_range_self s),hn s hs⟩)⟩

lemma fan_to_center_label [Finite ι] {F : ι → Arc ℂ} {d : Faces F} {a : Arc ℂ}
    (h₀ : a 0∈face F d) (hU : a '' Ioo (0:I) 1⊆face F d)
    {S : Set ℂ} (hS : range a⊆S) {q : ℂ} (hq : q∈⋃ i,range (F i))
    {f : ℂ → Bool} (hf : ContinuousOn f (S\{q})) {t : I} (ht : a t≠q) :
    f (a t)=f (a 0) := by
  apply (arc_label_interval a hf (nonneg t) ?_).symm
  intro s hs
  refine ⟨hS (mem_range_self s),?_⟩
  intro hsq
  have hs₁ : s=1 := by
    by_contra hn
    exact (fan_parameter_in_face h₀ hU hn).1 (hsq ▸ hq)
  have ht₁ : t=1 := le_antisymm (le_one t) (hs₁ ▸ hs.2)
  exact ht (ht₁.symm ▸ hs₁ ▸ hsq)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonPolygonal CannonFaceIncidence CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

theorem stellar_old_point_no_cut (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (hc : ∀ d,c d∈face F d)
    (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (h₀ : ∀ i,A i 0=c i.1) (h₁ : ∀ i,A i 1=i.2.val)
    (hU : ∀ i,A i '' Ioo (0:I) 1⊆face F i.1)
    {q : ℂ} (hq : q∈⋃ i,range (F i)) :
    IsPreconnected (((⋃ i,range (F i))∪(⋃ i,range (A i)))\{q}) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF P hP
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let K := ⋃ i,range (F i)
  let S := K∪⋃ i,range (A i)
  have hAS (i : Σ d : Faces F,faceVertices F d) : range (A i)⊆S :=
    fun z hz => Or.inr (mem_iUnion.mpr ⟨i,hz⟩)
  have hFS (i : ι) : range (F i)⊆S := fun z hz => Or.inl (mem_iUnion.mpr ⟨i,hz⟩)
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hnew (i : Σ d : Faces F,faceVertices F d) {t : I} (ht : A i t≠q) :
      f (A i t)=f (c i.1) := by
    have hh := fan_to_center_label (h₀ i ▸ hc i.1) (hU i) (hAS i) hq hf ht
    rwa [h₀ i] at hh
  have hold (d : Faces F) {z : ℂ} (hz : z∈closure (face F d)) (hzK : z∈K) (hzq : z≠q) :
      f z=f (c d) := by
    obtain ⟨i,⟨t,rfl⟩,hi⟩ := face_boundary_edges F hF P hP d hz hzK
    obtain ⟨e,he,heq,hlabel⟩ := arc_punctured_endpoint_label (F i) (hFS i) hf hzq
    have hv : F i e∈faceVertices F d := by
      apply (mem_faceVertices F d _).mpr
      refine ⟨⟨i,?_⟩,hi (mem_range_self e)⟩
      rcases he with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    let v : faceVertices F d := ⟨F i e,hv⟩
    have hh := hnew ⟨d,v⟩ (t:=1) (by simpa only [h₁] using heq)
    rw [h₁] at hh
    exact hlabel.trans hh
  have hcover : ∀ z : ℂ,∃ d : Faces F,z∈closure (face F d) := by
    intro z
    apply mem_iUnion.mp
    rw [face_closures_cover F hF P hP]
    exact mem_univ z
  have hlabels : ∀ d e : Faces F,f (c d)=f (c e) := by
    apply CannonClosedCover.labels_constant
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) q).isPreconnected
      (fun d => closure (face F d)) (fun _ => isClosed_closure)
      (fun z _ => mem_iUnion.mpr (hcover z))
      (fun d => ⟨c d,(fun he => (hc d).1 (he ▸ hq)),subset_closure (hc d)⟩) (fun d => f (c d))
    intro z hz d hzd e hze
    by_cases hzK : z∈K
    · exact (hold d hzd hzK hz).symm.trans (hold e hze hzK hz)
    · have hzd' := closure_region_inside
        (isClosed_iUnion_of_finite fun j => (F j).compact_range.isClosed).isOpen_compl
        ConnectedComponents.continuous_coe hzd hzK
      have hze' := closure_region_inside
        (isClosed_iUnion_of_finite fun j => (F j).compact_range.isClosed).isOpen_compl
        ConnectedComponents.continuous_coe hze hzK
      have hde : d=e := hzd'.2.symm.trans hze'.2
      rw [hde]
  have hpoint {z : ℂ} (hz : z∈S\{q}) : ∃ d : Faces F,f z=f (c d) := by
    rcases hz.1 with hzK|hzA
    · obtain ⟨d,hd⟩ := hcover z
      exact ⟨d,hold d hd hzK hz.2⟩
    · obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzA
      exact ⟨i.1,hnew i hz.2⟩
  obtain ⟨d,hd⟩ := hpoint hx
  obtain ⟨e,he⟩ := hpoint hy
  exact hd.trans ((hlabels d e).trans he.symm)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonPolygonal CannonFaceIncidence CannonSegmentCones

variable {ι : Type*} [Finite ι] [Nonempty ι]

lemma face_spoke_avoiding (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hA : Pairwise (fun i j => Compatible (A i) (A j)))
    (h₀ : ∀ i,A i 0=c i.1) (h₁ : ∀ i,A i 1=i.2.val)
    (d : Faces F) {q : ℂ} (hq : q∉⋃ i,range (F i)) (hqc : c d≠q) :
    ∃ v : faceVertices F d,q∉range (A ⟨d,v⟩) := by
  classical
  obtain ⟨x,hx,y,hy,hxy⟩ := faceVertices_nontrivial F hF P hP d
  let v : faceVertices F d := ⟨x,hx⟩
  let w : faceVertices F d := ⟨y,hy⟩
  by_cases hv : q∈range (A ⟨d,v⟩)
  swap
  · exact ⟨v,hv⟩
  refine ⟨w,?_⟩
  rintro ⟨t,ht⟩
  obtain ⟨s,hs⟩ := hv
  have hvw : (⟨d,v⟩ : Σ d : Faces F,faceVertices F d)≠⟨d,w⟩ := by
    intro h
    have hh := Sigma.mk.inj_iff.mp h
    have : v=w := eq_of_heq hh.2
    exact hxy (congrArg Subtype.val this)
  obtain ⟨he,_⟩ := (hA hvw).1 s t (hs.trans ht.symm)
  rcases he with rfl|rfl
  · exact hqc ((h₀ _).symm.trans hs)
  · apply hq
    rw [←hs,h₁]
    exact vertex_mem_support F ((mem_faceVertices F d x).mp hx).1

theorem stellar_new_point_no_cut (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsPreconnected (⋃ i,range (F i)))
    (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ)
    (hA : Pairwise (fun i j => Compatible (A i) (A j)))
    (h₀ : ∀ i,A i 0=c i.1) (h₁ : ∀ i,A i 1=i.2.val)
    {q : ℂ} (hq : q∉⋃ i,range (F i)) :
    IsPreconnected (((⋃ i,range (F i))∪(⋃ i,range (A i)))\{q}) := by
  classical
  let K := ⋃ i,range (F i)
  let S := K∪⋃ i,range (A i)
  have hKS : K⊆S\{q} := fun z hz => ⟨Or.inl hz,fun he => hq (he ▸ hz)⟩
  have hAS (i : Σ d : Faces F,faceVertices F d) : range (A i)⊆S :=
    fun z hz => Or.inr (mem_iUnion.mpr ⟨i,hz⟩)
  let i₀ : ι := Classical.choice inferInstance
  let b := F i₀ 0
  have hb : b∈K := mem_iUnion.mpr ⟨i₀,mem_range_self 0⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  have hold {z : ℂ} (hz : z∈K) : f z=f b := hK.constant (hf.mono hKS) hz hb
  have hcenter {d : Faces F} (hdq : c d≠q) : f (c d)=f b := by
    obtain ⟨v,hv⟩ := face_spoke_avoiding F hF P hP c A hA h₀ h₁ d hq hdq
    have hsub : range (A ⟨d,v⟩)⊆S\{q} := fun z hz =>
      ⟨hAS _ hz,fun he => hv (he ▸ hz)⟩
    have hh := (isPreconnected_range (A ⟨d,v⟩).continuous).constant (hf.mono hsub)
      (mem_range_self (0:I)) (mem_range_self (1:I))
    rw [h₀,h₁] at hh
    exact hh.trans (hold (vertex_mem_support F ((mem_faceVertices F d v.val).mp v.property).1))
  have hpoint {z : ℂ} (hz : z∈S\{q}) : f z=f b := by
    rcases hz.1 with hzK|hzA
    · exact hold hzK
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzA
    obtain ⟨e,he,heq,hlabel⟩ := arc_punctured_endpoint_label (A i) (hAS i) hf hz.2
    rcases he with rfl|rfl
    · rw [h₀] at heq hlabel
      exact hlabel.trans (hcenter heq)
    · rw [h₁] at hlabel
      exact hlabel.trans (hold (vertex_mem_support F ((mem_faceVertices F i.1 i.2.val).mp i.2.property).1))
  exact (hpoint hx).trans (hpoint hy).symm

theorem global_stellation_no_cut_points (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    (hK : IsPreconnected (⋃ i,range (F i))) :
    ∃ (c : Faces F → ℂ) (A : (Σ d : Faces F,faceVertices F d) → Arc ℂ),
      (∀ d,c d∈face F d) ∧
      Pairwise (fun i j => Compatible (Sum.elim F A i) (Sum.elim F A j)) ∧
      (∀ i,A i 0=c i.1) ∧ (∀ i,A i 1=i.2.val) ∧
      (∀ i,FiniteSupport (range (A i))) ∧
      (∀ i,A i '' Ioo (0:I) 1⊆face F i.1) ∧
      ∀ q : ℂ,IsPreconnected (((⋃ i,range (F i))∪(⋃ i,range (A i)))\{q}) := by
  obtain ⟨c,A,hc,hA,h₀,h₁,hS,hU⟩ := global_vertex_stellation F hF P hP
  refine ⟨c,A,hc,hA,h₀,h₁,hS,hU,?_⟩
  intro q
  by_cases hq : q∈⋃ i,range (F i)
  · exact stellar_old_point_no_cut F hF P hP c hc A h₀ h₁ hU hq
  · exact stellar_new_point_no_cut F hF P hP hK c A
      (fun _ _ hne => hA (fun h => hne (Sum.inr_injective h))) h₀ h₁ hq
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_interior_complement_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (e : ι)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    IsPreconnected ((⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  let m : I := ⟨1/2,by norm_num,by norm_num⟩
  have hm₀ : (0:I) < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < (1:I) := by change (1/2:ℝ)<1; norm_num
  let q := F e m
  let S : Set ℂ := (⋃ i,range (F i))\{q}
  have hR₀ : F e 0∈R := Or.inr (by simp)
  have hR₁ : F e 1∈R := Or.inr (by simp)
  have hRi (i : {i : ι // i≠e}) : range (F i.val)⊆R := fun z hz => Or.inl (mem_iUnion.mpr ⟨i,hz⟩)
  have hnot (i : {i : ι // i≠e}) : q∉range (F i.val) := by
    rintro ⟨t,ht⟩
    rcases ((hF i.property).1 t m ht).2 with h|h
    · exact hm₀.ne' h
    · exact hm₁.ne h
  have hRS : R⊆S := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion.mpr ⟨i.val,hzi⟩,fun he => hnot i (he ▸ hzi)⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 0⟩,fun he => hm₀.ne ((F e).injective he)⟩
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 1⟩,fun he => hm₁.ne ((F e).injective he).symm⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  let C : ({i : ι // i≠e}⊕Bool) → Set ℂ := Sum.elim (fun i => range (F i.val))
    (fun b => if b then F e '' Icc m (1:I) else F e '' Icc (0:I) m)
  let l : ({i : ι // i≠e}⊕Bool) → Bool := Sum.elim (fun i => f (F i.val 0))
    (fun b => if b then f (F e 1) else f (F e 0))
  have hclosed : ∀ j,IsClosed (C j) := by
    rintro (i|b)
    · exact (F i.val).compact_range.isClosed
    · cases b <;> exact (isCompact_Icc.image (F e).continuous).isClosed
  have hcover : S⊆⋃ j,C j := by
    rintro z ⟨hz,hzq⟩
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hz
    by_cases hi : i=e
    · subst i
      rcases le_total t m with ht|ht
      · exact mem_iUnion.mpr ⟨Sum.inr false,⟨t,⟨nonneg t,ht⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨Sum.inr true,⟨t,⟨ht,le_one t⟩,rfl⟩⟩
    · exact mem_iUnion.mpr ⟨Sum.inl ⟨i,hi⟩,mem_range_self t⟩
  have hne : ∀ j,(S∩C j).Nonempty := by
    rintro (i|b)
    · exact ⟨F i.val 0,hRS (hRi i (mem_range_self 0)),mem_range_self 0⟩
    · cases b
      · exact ⟨F e 0,hRS hR₀,⟨0,⟨le_rfl,hm₀.le⟩,rfl⟩⟩
      · exact ⟨F e 1,hRS hR₁,⟨1,⟨hm₁.le,le_rfl⟩,rfl⟩⟩
  have hlabel (i : {i : ι // i≠e}) {z : ℂ} (hz : z∈C (Sum.inl i)) :
      f z=l (Sum.inl i) :=
    (isPreconnected_range (F i.val).continuous).constant (hf.mono (hRi i)) hz (mem_range_self 0)
  have holdnew (i : {i : ι // i≠e}) (b : Bool) {z : ℂ}
      (hzi : z∈C (Sum.inl i)) (hzb : z∈C (Sum.inr b)) :
      l (Sum.inl i)=l (Sum.inr b) := by
    obtain ⟨s,rfl⟩ := hzi
    cases b
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₀ : t=0 := ((hF i.property).1 s t he.symm).2.resolve_right
        (fun h => hm₁.not_ge (h ▸ ht.2))
      have hz : F i.val s=F e 0 := ht₀ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₁ : t=1 := ((hF i.property).1 s t he.symm).2.resolve_left
        (fun h => hm₀.not_ge (h ▸ ht.1))
      have hz : F i.val s=F e 1 := ht₁ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
  have hall : ∀ i j,l i=l j := by
    apply CannonClosedCover.labels_constant (hK q) C hclosed hcover hne l
    intro z hz i hzi j hzj
    rcases i with i|b <;> rcases j with j|c
    · exact (hlabel i hzi).symm.trans (hlabel j hzj)
    · exact holdnew i c hzi hzj
    · exact (holdnew j b hzj hzi).symm
    · cases b <;> cases c
      · rfl
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm hs.2 (hts ▸ ht.1)
        exact (hz.2 (congrArg (F e) hsm)).elim
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm (hts ▸ ht.2) hs.1
        exact (hz.2 (congrArg (F e) hsm)).elim
      · rfl
  have hvalue {z : ℂ} (hz : z∈R) : f z=l (Sum.inr false) := by
    rcases hz with hz|hz
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact (hlabel i hzi).trans (hall _ _)
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · rfl
      · exact hall (Sum.inr true) _
  exact (hvalue hx).trans (hvalue hy).symm
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_on_tame_cycle (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ b : Arc ℂ,b 0=F e 0 ∧ b 1=F e 1 ∧
      range b⊆⋃ i,range (F i) ∧ FiniteSupport (range b) ∧
      ∀ s t,F e s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  have hR : IsPreconnected R := edge_interior_complement_preconnected F hF e hK
  obtain ⟨P,hP⟩ := finite_graph_exact_segments (fun i : {i : ι // i≠e} => F i.val) Q (fun i => hQ i.val)
  let T := P∪{(F e 0,F e 0),(F e 1,F e 1)}
  have hT : R=⋃ p∈T,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hP]
    apply congrArg (fun S : Set ℂ => (⋃ i : {i : ι // i≠e},range (F i.val))∪S)
    ext z
    constructor
    · intro hz
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion₂.mpr ⟨(F e 0,F e 0),Finset.mem_insert_self ..,left_mem_segment ..⟩
      · exact mem_iUnion₂.mpr ⟨(F e 1,F e 1),Finset.mem_insert_of_mem (Finset.mem_singleton_self _),left_mem_segment ..⟩
    · intro hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      rcases Finset.mem_insert.mp hp with rfl|hp
      · exact Or.inl (by simpa only [segment_same,mem_singleton_iff] using hz)
      · have hp' := Finset.mem_singleton.mp hp
        subst p
        exact Or.inr (by simpa only [segment_same,mem_singleton_iff] using hz)
  obtain ⟨b,hb₀,hb₁,hbT,hbS⟩ := preconnected_finite_segments_arc T (hT ▸ hR)
    (hT ▸ (show F e 0∈R from Or.inr (by simp)))
    (hT ▸ (show F e 1∈R from Or.inr (by simp))) (F e).endpoints_ne
  have hbR : range b⊆R := by rwa [←hT] at hbT
  have hRK : R⊆⋃ i,range (F i) := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i.val,hzi⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion.mpr ⟨e,mem_range_self 0⟩
      · exact mem_iUnion.mpr ⟨e,mem_range_self 1⟩
  refine ⟨b,hb₀,hb₁,hbR.trans hRK,hbS,?_⟩
  intro s t he
  have hs : s=0 ∨ s=1 := by
    have hbs : F e s∈R := he.symm ▸ hbR (mem_range_self t)
    rcases hbs with hbs|hbs
    · obtain ⟨i,u,hu⟩ := mem_iUnion.mp hbs
      exact ((hF i.property).1 u s hu).2
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hbs : F e s=F e 0 ∨ F e s=F e 1) with h|h
      · exact Or.inl ((F e).injective h)
      · exact Or.inr ((F e).injective h)
  refine ⟨hs,?_⟩
  rcases hs with rfl|rfl
  · exact Or.inl (b.injective (he.symm.trans hb₀.symm))
  · exact Or.inr (b.injective (he.symm.trans hb₁.symm))
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
