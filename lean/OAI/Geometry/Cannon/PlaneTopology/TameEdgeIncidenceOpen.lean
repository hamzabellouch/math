import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.ComponentRegion
import OAI.Geometry.Cannon.PlaneTopology.RadialStable
import OAI.Geometry.Cannon.Energy.OpenPreconnectedRemovePoint

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
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_in_open (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ W : Set ℂ, IsOpen W ∧ F i t∈W ∧ ∃ l : Bool → D,
      ∀ x∈W∩(⋃ j,range (F j)), incident (U\(⋃ j,range (F j))) π x=range l := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart F hF Q hQ i ht₀ ht₁
  have htU : F i t∈U := hiU ⟨t,⟨ht₀,ht₁⟩,rfl⟩
  have hf : ∀ z∈W∩U, z∈U\(⋃ j,range (F j)) ↔ (H.symm z).2≠0 := by
    intro z hz
    have he : z∈(⋃ j,range (F j)) ↔ (H.symm z).2=0 := by
      rw [hflat z hz.1,H.image_eq_preimage_symm]
      rfl
    simp only [mem_sdiff,hz.2,true_and,he]
  obtain ⟨W',hW',h₀W',_,l,hl⟩ := flat_chart_incidence hπ H (hW.inter hU)
    (h₀.symm ▸ ⟨htW,htU⟩) hf
  exact ⟨W',hW',h₀ ▸ h₀W',l,fun x hx => hl x ⟨hx.1,fun h => h.2 hx.2⟩⟩

theorem tame_edge_labels_in_open (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) :
    ∃ l : Bool → D, ∀ t : I, 0<t → t<1 →
      incident (U\(⋃ j,range (F j))) π (F i t)=range l := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A := isPreconnected_Ioo.image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ W : Set ℂ, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨W,hW,htW,l,hl⟩ := tame_edge_incidence_in_open F hF Q hQ hU hπ i hiU ht.1 ht.2
    refine ⟨W,hW,htW,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyW⟩
    exact (hl y ⟨hyW,mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩⟩).trans
      (hl (F i t) ⟨htW,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; norm_num
  obtain ⟨W,hW,hmW,l,hl⟩ := tame_edge_incidence_in_open F hF Q hQ hU hπ i hiU hm.1 hm.2
  refine ⟨l,fun t ht₀ ht₁ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₀,ht₁⟩,rfl⟩
    (F i m) ⟨m,hm,rfl⟩).trans (hl (F i m) ⟨hmW,mem_iUnion.mpr ⟨i,mem_range_self m⟩⟩)

theorem tame_star_center_incident [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (x : ℂ) (hx : x∈U) (h₀ : ∀ i, F i 0=x) (h₁ : ∀ i, F i 1∉U)
    (hFU : ∀ i, F i '' Ioo (0:I) 1⊆U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region (U\(⋃ j,range (F j))) π d).Nonempty) :
    d∈incident (U\(⋃ j,range (F j))) π x := by
  let K := ⋃ j,range (F j)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  have hxK : x∈K := by obtain ⟨i⟩ := ‹Nonempty ι›; exact mem_iUnion.mpr ⟨i,⟨0,h₀ i⟩⟩
  have hne : (U\(U\K)).Nonempty := ⟨x,hx,fun hxV => hxV.2 hxK⟩
  obtain ⟨y,⟨hyU,hyV⟩,hyd⟩ := region_boundary_hits_in_open
    hU (hU.sdiff hK) sdiff_subset hconn hne hπ d hd
  by_cases hyx : y=x
  · subst y
    exact hyd
  have hyK : y∈K := by by_contra hn; exact hyV ⟨hyU,hn⟩
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hyK
  have ht₀ : t≠0 := fun ht => hyx (ht ▸ h₀ i)
  have ht₁ : t≠1 := fun h => h₁ i (h ▸ hyU)
  obtain ⟨l,hl⟩ := tame_edge_labels_in_open F hF Q hQ hU hπ i (hFU i)
  have hdR : d∈range l := by
    rw [←hl t (lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) ht₀.symm)
      (lt_of_le_of_ne (le_one t) ht₁)]
    exact hyd
  have hclosed : IsClosed ((F i) ⁻¹' closure (region (U\K) π d)) :=
    isClosed_closure.preimage (F i).continuous
  have hs : Ioo (0:I) 1⊆(F i) ⁻¹' closure (region (U\K) π d) := by
    intro t ht
    show d∈incident (U\K) π (F i t)
    rw [hl t ht.1 ht.2]
    exact hdR
  have hz : (0:I)∈closure (Ioo (0:I) 1) := by
    rw [closure_Ioo (by exact zero_ne_one)]
    exact ⟨le_rfl,zero_le_one⟩
  have he := closure_minimal hs hclosed hz
  change x∈closure (region (U\K) π d)
  simpa only [mem_preimage,h₀ i] using he
end CannonEmbeddedArc.Arc

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma FiniteSupport.iUnion {ι : Type*} [Finite ι] {S : ι → Set E}
    (hS : ∀ i, FiniteSupport (S i)) : FiniteSupport (⋃ i,S i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP using hS
  refine ⟨Finset.univ.biUnion P,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hP i hi)
  exact mem_iUnion₂.mpr ⟨p,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩,hxp⟩
end CannonPolygonal

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

lemma finite_segment_union (P Q : Finset (ℂ × ℂ)) :
    (⋃ p∈P∪Q,segment ℝ p.1 p.2)=(⋃ p∈P,segment ℝ p.1 p.2)∪(⋃ p∈Q,segment ℝ p.1 p.2) := by
  ext x
  simp only [mem_iUnion,Finset.mem_union,mem_union]
  constructor
  · rintro ⟨p,hp,hx⟩
    exact hp.elim (fun h => Or.inl ⟨p,h,hx⟩) (fun h => Or.inr ⟨p,h,hx⟩)
  · rintro (⟨p,hp,hx⟩|⟨p,hp,hx⟩)
    · exact ⟨p,Or.inl hp,hx⟩
    · exact ⟨p,Or.inr hp,hx⟩

theorem extend_tame_star {ι : Type*} [Finite ι] [Nonempty ι]
    (P : Finset (ℂ × ℂ)) {a x y : ℂ}
    (ha : a∉⋃ p∈P,segment ℝ p.1 p.2)
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2)
    (hycl : y∈closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a))
    (F : ι → Arc ℂ) (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (hS : ∀ i,FiniteSupport (range (F i)))
    (h₀ : ∀ i,F i 0=x)
    (h₁ : ∀ i,F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hny : ∀ i,F i 1≠y)
    (hFU : ∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (c '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      ∀ i,Compatible c (F i) := by
  classical
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  let G := ⋃ i,range (F i)
  have hK : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUK : U⊆Kᶜ := connectedComponentIn_subset _ _
  have hyU : y∉U := fun hh => hUK hh hy
  have hxy : x≠y := fun he => hyU (he ▸ hx)
  obtain ⟨Q,hQ⟩ := FiniteSupport.iUnion hS
  have hQi (i : ι) : range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2 :=
    fun z hz => hQ (mem_iUnion.mpr ⟨i,hz⟩)
  obtain ⟨R,hR⟩ := finite_graph_exact_segments F Q hQi
  let L := K∪G
  have hL : L=⋃ p∈P∪R,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hR]
  have hKL : (⋃ p∈P,segment ℝ p.1 p.2)⊆⋃ p∈P∪R,segment ℝ p.1 p.2 := by
    rw [←hL]
    exact subset_union_left
  obtain ⟨z,hzU,hzL,hycl',hsubU⟩ := refined_component_at_boundary P (P∪R) hKL ha hycl
  rw [←hL] at hzL hycl' hsubU
  have hzG : z∉G := fun hh => hzL (Or.inr hh)
  let V := U\G
  have hV : IsOpen V := hU.sdiff (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed)
  have hzV : z∈V := ⟨hzU,hzG⟩
  have hVL : V⊆Lᶜ := by
    rintro w ⟨hwU,hwG⟩ (hwK|hwG')
    · exact hUK hwU hwK
    · exact hwG hwG'
  have hcomp : connectedComponentIn V z=connectedComponentIn Lᶜ z := by
    apply subset_antisymm (connectedComponentIn_mono z hVL)
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzL)
    intro w hw
    exact ⟨hsubU hw,fun hwG => connectedComponentIn_subset _ _ hw (Or.inr hwG)⟩
  let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents V) := inferInstance
  have hxcl' := tame_star_center_incident F hF Q hQi hU isPreconnected_connectedComponentIn
    x hx h₀ h₁ hFU ConnectedComponents.continuous_coe
    (ConnectedComponents.mk (⟨z,hzV⟩ : V)) ⟨z,hzV,rfl⟩
  change x∈closure (region V ConnectedComponents.mk (ConnectedComponents.mk (⟨z,hzV⟩ : V))) at hxcl'
  rw [component_region_eq,hcomp] at hxcl'
  have hxG : x∈G := by
    let i : ι := Classical.choice inferInstance
    exact mem_iUnion.mpr ⟨i,0,h₀ i⟩
  have hxL : x∈L := Or.inr hxG
  have hyL : y∈L := Or.inl hy
  rw [hL] at hxL hyL hxcl' hycl'
  obtain ⟨c,hc₀,hc₁,hcU,hcS⟩ := finite_segment_component_crosscut (P∪R) hxL hyL hxy hxcl' hycl'
  have hcV (t : I) (ht₀ : t≠0) (ht₁ : t≠1) : c t∈V := by
    have hh := hcU t ht₀ ht₁
    rw [←hL,←hcomp] at hh
    exact connectedComponentIn_subset _ _ hh
  have hyG : y∉G := by
    intro hyG
    obtain ⟨i,t,he⟩ := mem_iUnion.mp hyG
    by_cases ht₀ : t=0
    · exact hxy ((h₀ i).symm.trans (ht₀ ▸ he))
    by_cases ht₁ : t=1
    · exact hny i (ht₁ ▸ he)
    exact hyU (he ▸ hFU i ⟨t,⟨lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) (Ne.symm ht₀),
      lt_of_le_of_ne (le_one t) ht₁⟩,rfl⟩)
  have hinter (i : ι) (s t : I) (he : c s=F i t) : s=0 ∧ t=0 := by
    have hs : s=0 := by
      by_contra hs
      by_cases hs₁ : s=1
      · exact hyG (mem_iUnion.mpr ⟨i,t,he.symm.trans (hs₁ ▸ hc₁)⟩)
      · exact (hcV s hs hs₁).2 (mem_iUnion.mpr ⟨i,t,he.symm⟩)
    refine ⟨hs,(F i).injective ?_⟩
    exact he.symm.trans ((hs ▸ hc₀).trans (h₀ i).symm)
  refine ⟨c,hc₀,hc₁,hcS,?_,fun i => ?_⟩
  · rintro w ⟨t,ht,rfl⟩
    exact (hcV t ht.1.ne' ht.2.ne).1
  · refine ⟨fun s t he => ⟨Or.inl (hinter i s t he).1,Or.inl (hinter i s t he).2⟩,?_⟩
    rintro w ⟨⟨s,rfl⟩,t,he⟩ w' ⟨⟨s',rfl⟩,t',he'⟩
    rw [(hinter i s t he.symm).1,(hinter i s' t' he'.symm).1]
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem finite_tame_star (P : Finset (ℂ × ℂ)) {a x : ℂ}
    (ha : a∉⋃ p∈P,segment ℝ p.1 p.2)
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (B : Finset ℂ) (hB : ∀ y∈B,y∈(⋃ p∈P,segment ℝ p.1 p.2) ∩
      closure (connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)) :
    ∃ F : B → Arc ℂ, Pairwise (fun i j => Compatible (F i) (F j)) ∧
      (∀ i,F i 0=x) ∧ (∀ i,F i 1=i.val) ∧
      (∀ i,FiniteSupport (range (F i))) ∧
      (∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) := by
  classical
  let K := ⋃ p∈P,segment ℝ p.1 p.2
  let U := connectedComponentIn Kᶜ a
  have hK : IsClosed K := isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUK : U⊆Kᶜ := connectedComponentIn_subset _ _
  induction B using Finset.induction_on with
  | empty =>
    refine ⟨fun i => False.elim ((Finset.notMem_empty i.val) i.property),?_,?_,?_,?_,?_⟩ <;>
      intro i <;> exact ((Finset.notMem_empty i.val) i.property).elim
  | @insert y B hy ih =>
    obtain ⟨F,hF,h₀,h₁,hS,hFU⟩ := ih (fun z hz => hB z (Finset.mem_insert_of_mem hz))
    have hyK := (hB y (Finset.mem_insert_self _ _)).1
    have hycl := (hB y (Finset.mem_insert_self _ _)).2
    have hyU : y∉U := fun h => hUK h hyK
    have hF₁ (i : B) : F i 1∉U := by
      rw [h₁]
      exact fun h => hUK h (hB i.val (Finset.mem_insert_of_mem i.property)).1
    have hny (i : B) : F i 1≠y := by
      rw [h₁]
      exact fun h => hy (h ▸ i.property)
    obtain ⟨c,hc₀,hc₁,hcS,hcU,hcF⟩ : ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧
        FiniteSupport (range c) ∧ (c '' Ioo (0:I) 1⊆U) ∧ ∀ i,Compatible c (F i) := by
      by_cases hn : Nonempty B
      · let _ : Nonempty B := hn
        exact extend_tame_star P ha hx hyK hycl F hF hS h₀ hF₁ hny hFU
      · have hxy : x≠y := fun he => hyU (he ▸ hx)
        obtain ⟨b,_,hb⟩ := component_radial_access P hyK hycl
        obtain ⟨c,hc₀,hc₁,hcU,hcS⟩ := arc_between_accessible_points hU
          isPreconnected_connectedComponentIn hxy (a:=x)
          (fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using (show x∈U from hx)) hb
        refine ⟨c,hc₀,hc₁,hcS,?_,fun i => (hn ⟨i⟩).elim⟩
        rintro z ⟨t,ht,rfl⟩
        exact hcU t ht.1.ne' ht.2.ne
    let F' : ↥(insert y B : Finset ℂ) → Arc ℂ := fun i =>
      if h : i.val=y then c else F ⟨i.val,(Finset.mem_insert.mp i.property).resolve_left h⟩
    have hiold (i : (insert y B : Finset ℂ)) (h : i.val≠y) : i.val∈B :=
      (Finset.mem_insert.mp i.property).resolve_left h
    have hnew (i : (insert y B : Finset ℂ)) (h : i.val=y) : F' i=c := by simp [F',h]
    have hold (i : (insert y B : Finset ℂ)) (h : i.val≠y) : F' i=F ⟨i.val,hiold i h⟩ := by simp [F',h]
    refine ⟨F',?_,?_,?_,?_,?_⟩
    · intro i j hij
      by_cases hi : i.val=y
      · rw [hnew i hi]
        by_cases hj : j.val=y
        · exact (hij (Subtype.ext (hi.trans hj.symm))).elim
        · rw [hold j hj]
          exact hcF _
      · rw [hold i hi]
        by_cases hj : j.val=y
        · rw [hnew j hj]
          exact (hcF _).symm
        · rw [hold j hj]
          exact hF (fun h => hij (Subtype.ext (congrArg (fun b : B => b.val) h)))
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hc₀
      · rw [hold i hi]; exact h₀ _
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hc₁.trans hi.symm
      · rw [hold i hi]; exact h₁ _
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hcS
      · rw [hold i hi]; exact hS _
    · intro i
      by_cases hi : i.val=y
      · rw [hnew i hi]; exact hcU
      · rw [hold i hi]; exact hFU _
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {X : Type*} [TopologicalSpace X] [T2Space X]
theorem isolate_edge_interior_weak {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (i : ι) {p t q : I} (hpt : p<t) (htq : t<q) :
    ∃ W : Set X, IsOpen W ∧ F i t∈W ∧
      ∀ z∈W, (z∈⋃ j, range (F j) ↔ z∈F i '' Icc p q) := by
  classical
  let A : Set X := ⋃ j : {j // j≠i}, range (F j.val)
  let B : Set X := F i '' (Iic p∪Ici q)
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun j => (F j.val).compact_range.isClosed)
  have hB : IsClosed B :=
    ((isClosed_Iic.union isClosed_Ici).isCompact.image (F i).continuous).isClosed
  let W := (A∪B)ᶜ
  have ht₀ : t≠0 := ne_of_gt ((unitInterval.nonneg p).trans_lt hpt)
  have ht₁ : t≠1 := ne_of_lt (htq.trans_le (unitInterval.le_one q))
  have htA : F i t∉A := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    obtain ⟨s,hs⟩ := hj
    have hh := (hF j.property.symm) t s hs.symm
    exact hh.1.elim ht₀ ht₁
  have htB : F i t∉B := by
    rintro ⟨s,hs,hst⟩
    have he := (F i).injective hst
    subst s
    exact hs.elim hpt.not_ge htq.not_ge
  refine ⟨W,(hA.union hB).isOpen_compl,fun h => h.elim htA htB,?_⟩
  intro z hz
  constructor
  · intro hzF
    obtain ⟨j,s,hs⟩ := mem_iUnion.mp hzF
    by_cases hji : j=i
    · subst j
      refine ⟨s,?_,hs⟩
      have hsB : s∉Iic p∪Ici q := fun hsB => hz (Or.inr ⟨s,hsB,hs⟩)
      constructor
      · exact (lt_of_not_ge (fun h => hsB (Or.inl h))).le
      · exact (lt_of_not_ge (fun h => hsB (Or.inr h))).le
    · exact (hz (Or.inl (mem_iUnion.mpr ⟨⟨j,hji⟩,⟨s,hs⟩⟩))).elim
  · rintro ⟨s,_,rfl⟩
    exact mem_iUnion.mpr ⟨i,mem_range_self s⟩
end CannonEmbeddedArc.Arc
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

theorem tame_graph_flat_chart_weak {ι : Type*} [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ F i t∈W ∧
      H (0,0)=F i t ∧ ∀ z∈W,
        (z∈⋃ j, range (F j) ↔ z∈H '' horizontal) := by
  obtain ⟨p,q,hpt,htq,hleft,hright,hcorner⟩ := tame_interior_corner Q (F i) (hQ i) ht₀ ht₁
  obtain ⟨W,hW,htW,hiso⟩ := isolate_edge_interior_weak F hF i hpt htq
  let x := F i t
  let u := F i p-x
  let v := F i q-x
  have hu : u≠0 := sub_ne_zero.mpr ((F i).injective.ne hpt.ne)
  have hv : v≠0 := sub_ne_zero.mpr ((F i).injective.ne htq.ne.symm)
  let r := min ‖u‖ ‖v‖
  have hr : 0<r := lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  obtain ⟨H₀,hH₀,hHr⟩ := straighten_corner hcorner
  let H := H₀.trans (Homeomorph.addLeft x)
  refine ⟨H,W∩ball x r,hW.inter isOpen_ball,⟨htW,mem_ball_self hr⟩,?_,?_⟩
  · simp [H,hH₀,x]
  · intro z hz
    rw [hiso z hz.1]
    have he : Icc p q=Icc p t∪Icc t q := by
      ext s
      constructor
      · intro hs
        rcases le_total s t with hst|hts
        · exact Or.inl ⟨hs.1,hst⟩
        · exact Or.inr ⟨hts,hs.2⟩
      · rintro (hs|hs)
        · exact ⟨hs.1,hs.2.trans htq.le⟩
        · exact ⟨hpt.le.trans hs.1,hs.2⟩
    rw [he,image_union,hleft,hright]
    have hHimage : H '' horizontal=(fun w : ℂ => x+w) '' (ray u∪ray v) := by
      change ((fun w : ℂ => x+w) ∘ H₀) '' horizontal=_
      rw [image_comp,hHr]
    rw [hHimage,image_union,mem_union,mem_union]
    have hxU : x+u=F i p := by dsimp [u,x]; abel
    have hxV : x+v=F i q := by dsimp [v,x]; abel
    have hmem (w : ℂ) : z∈(fun b : ℂ => x+b) '' ray w ↔
        ∃ s : ℝ, 0 ≤ s ∧ z = x+s•w := by
      constructor
      · rintro ⟨b,⟨s,hs,hb⟩,hbe⟩
        exact ⟨s,hs,by rw [hb] at hbe; exact hbe.symm⟩
      · rintro ⟨s,hs,rfl⟩
        exact ⟨s•w,⟨s,hs,rfl⟩,rfl⟩
    rw [hmem u,hmem v,local_ray_segment (min_le_left _ _) hz.2,
      local_ray_segment (min_le_right _ _) hz.2,hxU,hxV]
    rw [segment_symm (𝕜:=ℝ) (x:=F i p) (y:=x)]
end CannonEmbeddedArc.Arc
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_in_open_weak (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ W : Set ℂ, IsOpen W ∧ F i t∈W ∧ ∃ l : Bool → D,
      ∀ x∈W∩(⋃ j,range (F j)), incident (U\(⋃ j,range (F j))) π x=range l := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart_weak F hF Q hQ i ht₀ ht₁
  have htU : F i t∈U := hiU ⟨t,⟨ht₀,ht₁⟩,rfl⟩
  have hf : ∀ z∈W∩U, z∈U\(⋃ j,range (F j)) ↔ (H.symm z).2≠0 := by
    intro z hz
    have he : z∈(⋃ j,range (F j)) ↔ (H.symm z).2=0 := by
      rw [hflat z hz.1,H.image_eq_preimage_symm]
      rfl
    simp only [mem_sdiff,hz.2,true_and,he]
  obtain ⟨W',hW',h₀W',_,l,hl⟩ := flat_chart_incidence hπ H (hW.inter hU)
    (h₀.symm ▸ ⟨htW,htU⟩) hf
  exact ⟨W',hW',h₀ ▸ h₀W',l,fun x hx => hl x ⟨hx.1,fun h => h.2 hx.2⟩⟩

theorem tame_edge_labels_in_open_weak (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) (hiU : F i '' Ioo (0:I) 1⊆U) :
    ∃ l : Bool → D, ∀ t : I, 0<t → t<1 →
      incident (U\(⋃ j,range (F j))) π (F i t)=range l := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A := isPreconnected_Ioo.image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ W : Set ℂ, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨W,hW,htW,l,hl⟩ := tame_edge_incidence_in_open_weak F hF Q hQ hU hπ i hiU ht.1 ht.2
    refine ⟨W,hW,htW,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyW⟩
    exact (hl y ⟨hyW,mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩⟩).trans
      (hl (F i t) ⟨htW,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm : 0 < m ∧ m<1 := by change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1; norm_num
  obtain ⟨W,hW,hmW,l,hl⟩ := tame_edge_incidence_in_open_weak F hF Q hQ hU hπ i hiU hm.1 hm.2
  refine ⟨l,fun t ht₀ ht₁ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₀,ht₁⟩,rfl⟩
    (F i m) ⟨m,hm,rfl⟩).trans (hl (F i m) ⟨hmW,mem_iUnion.mpr ⟨i,mem_range_self m⟩⟩)

theorem tame_star_center_incident_weak [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I, F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (x : ℂ) (hx : x∈U) (h₀ : ∀ i, F i 0=x) (h₁ : ∀ i, F i 1∉U)
    (hFU : ∀ i, F i '' Ioo (0:I) 1⊆U)
    {π : (U\(⋃ j,range (F j)) : Set ℂ) → D} (hπ : Continuous π)
    (d : D) (hd : (region (U\(⋃ j,range (F j))) π d).Nonempty) :
    d∈incident (U\(⋃ j,range (F j))) π x := by
  let K := ⋃ j,range (F j)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed
  have hxK : x∈K := by obtain ⟨i⟩ := ‹Nonempty ι›; exact mem_iUnion.mpr ⟨i,⟨0,h₀ i⟩⟩
  have hne : (U\(U\K)).Nonempty := ⟨x,hx,fun hxV => hxV.2 hxK⟩
  obtain ⟨y,⟨hyU,hyV⟩,hyd⟩ := region_boundary_hits_in_open
    hU (hU.sdiff hK) sdiff_subset hconn hne hπ d hd
  by_cases hyx : y=x
  · subst y
    exact hyd
  have hyK : y∈K := by by_contra hn; exact hyV ⟨hyU,hn⟩
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hyK
  have ht₀ : t≠0 := fun ht => hyx (ht ▸ h₀ i)
  have ht₁ : t≠1 := fun h => h₁ i (h ▸ hyU)
  obtain ⟨l,hl⟩ := tame_edge_labels_in_open_weak F hF Q hQ hU hπ i (hFU i)
  have hdR : d∈range l := by
    rw [←hl t (lt_of_le_of_ne (show (0:I) ≤ t from t.property.1) ht₀.symm)
      (lt_of_le_of_ne (le_one t) ht₁)]
    exact hyd
  have hclosed : IsClosed ((F i) ⁻¹' closure (region (U\K) π d)) :=
    isClosed_closure.preimage (F i).continuous
  have hs : Ioo (0:I) 1⊆(F i) ⁻¹' closure (region (U\K) π d) := by
    intro t ht
    show d∈incident (U\K) π (F i t)
    rw [hl t ht.1 ht.2]
    exact hdR
  have hz : (0:I)∈closure (Ioo (0:I) 1) := by
    rw [closure_Ioo (by exact zero_ne_one)]
    exact ⟨le_rfl,zero_le_one⟩
  have he := closure_minimal hs hclosed hz
  change x∈closure (region (U\K) π d)
  simpa only [mem_preimage,h₀ i] using he
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem arc_with_terminal_germ {U C : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y w z : ℂ} (hxy : x≠y) (hy : y∉U)
    (hax : ∀ t : ℝ, 0<t → t≤1 → x+t • (w-x)∈U)
    (hby : ∀ t : ℝ, 0<t → t≤1 → y+t • (z-y)∈U∩C) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (∀ t : I,t≠0 → t≠1 → c t∈U) ∧
      ∃ ε : ℝ,0<ε ∧ range c∩ball y ε⊆insert y C := by
  have hz : z∈U := by simpa using (hby 1 zero_lt_one le_rfl).1
  have hzy : z≠y := fun h => hy (h ▸ hz)
  have hseg : segment ℝ y z⊆insert y (U∩C) := halfopen_radial_segment hby
  by_cases hxz : x=z
  · subst x
    let c := lineArc z y hzy
    refine ⟨c,by simp [c],by simp [c],?_,?_,1,zero_lt_one,?_⟩
    · rw [show range c=segment ℝ z y by exact lineArc_range ..]
      exact FiniteSupport.segment z y
    · intro t ht₀ ht₁
      have hm : c t∈segment ℝ y z := by rw [segment_symm,←lineArc_range z y hzy]; exact mem_range_self t
      rcases hseg hm with hm|hm
      · exact (ht₁ (c.injective (hm.trans (show c 1=y by simp [c]).symm))).elim
      · exact hm.1
    · intro q hq
      have hm : q∈segment ℝ y z := by
        have hh := hq.1
        rwa [show range c=segment ℝ z y by exact lineArc_range ..,segment_symm] at hh
      exact (hseg hm).imp id And.right
  obtain ⟨b,hb₀,hb₁,hbU,hbS⟩ := arc_between_accessible_points hU hc hxz hax
    (a:=w) (b:=z) (fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using hz)
  have hyb : y∉range b := by
    rintro ⟨t,ht⟩
    by_cases ht₀ : t=0
    · exact hxy (hb₀.symm.trans (ht₀ ▸ ht))
    by_cases ht₁ : t=1
    · exact hy ((ht₁ ▸ ht) ▸ hb₁.symm ▸ hz)
    exact hy (ht ▸ hbU t ht₀ ht₁)
  let d := lineArc z y hzy
  obtain ⟨c,hc₀,hc₁,hcr⟩ := extend_arc b d (by simpa [d] using hb₁) (by simpa [d] using hyb)
  have hc₀' : c 0=x := hc₀.trans hb₀
  have hc₁' : c 1=y := by simpa [d] using hc₁
  have hdr : range d=segment ℝ y z := by rw [lineArc_range,segment_symm]
  have hr : range b⊆insert x U := by
    rintro q ⟨t,rfl⟩
    by_cases ht₀ : t=0
    · exact Or.inl (ht₀ ▸ hb₀)
    by_cases ht₁ : t=1
    · exact Or.inr (ht₁ ▸ hb₁.symm ▸ hz)
    exact Or.inr (hbU t ht₀ ht₁)
  obtain ⟨ε,hε,havoid⟩ := Metric.isOpen_iff.mp b.compact_range.isClosed.isOpen_compl y hyb
  refine ⟨c,hc₀',hc₁',?_,?_,ε,hε,?_⟩
  · apply (hbS.union (FiniteSupport.segment y z)).mono
    simpa only [hdr] using hcr
  · intro t ht₀ ht₁
    rcases hcr (mem_range_self t) with hh|hh
    · rcases hr hh with hh|hh
      · exact (ht₀ (c.injective (hh.trans hc₀'.symm))).elim
      · exact hh
    · rw [hdr] at hh
      rcases hseg hh with hh|hh
      · exact (ht₁ (c.injective (hh.trans hc₁'.symm))).elim
      · exact hh.1
  · rintro q ⟨hq,hqball⟩
    rcases hcr hq with hh|hh
    · exact (havoid hqball hh).elim
    · rw [hdr] at hh
      exact (hseg hh).imp id And.right
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
