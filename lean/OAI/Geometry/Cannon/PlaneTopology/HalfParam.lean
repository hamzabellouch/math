import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.FiniteVertexSet
import OAI.Geometry.Cannon.PlaneTopology.TameEdgeIncidenceOpen

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
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

theorem extend_star_in_sector {ι : Type*} [Finite ι]
    (P : Finset (ℂ × ℂ)) {a x y : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hy : y∈⋃ p∈P,segment ℝ p.1 p.2)
    (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)))
    (hS : ∀ i,FiniteSupport (range (F i))) (h₀ : ∀ i,F i 0=x)
    (h₁ : ∀ i,F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hFU : ∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (C : Set ℂ) (hC : IsOpen C) (hyC : y∈closure C)
    (hCU : C⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ z∈C,∀ t : ℝ,0<t → t≤1 → y+t • (z-y)∈C) :
    ∃ c : Arc ℂ, c 0=x ∧ c 1=y ∧ FiniteSupport (range c) ∧
      (c '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      (∀ i,∀ s t : I,c s=F i t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      ∃ ε : ℝ,0<ε ∧ range c∩ball y ε⊆insert y C := by
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
  have hL : L=⋃ p∈P∪R,segment ℝ p.1 p.2 := by rw [finite_segment_union,←hR]
  have hLc : IsClosed L := by rw [hL]; exact isClosed_biUnion_finset fun p _ => segment_closed p.1 p.2
  obtain ⟨r,hr,hstable⟩ := finite_segments_radial_stable (P∪R) y
  have hne : (ball y r∩C).Nonempty := mem_closure_iff_nhds.mp hyC _ (ball_mem_nhds y hr)
  obtain ⟨z,⟨hzball,hzC⟩,hzL⟩ := (complex_finite_segments_compl_dense (P∪R)).inter_open_nonempty
    _ (isOpen_ball.inter hC) hne
  rw [←hL] at hzL
  have hzU : z∈U := hCU hzC
  let Z := connectedComponentIn Lᶜ z
  have hZU : Z⊆U := by
    have hs := connectedComponentIn_mono z (show Lᶜ⊆Kᶜ from compl_subset_compl.mpr subset_union_left)
    rwa [←connectedComponentIn_eq hzU] at hs
  have hzrad (t : ℝ) (ht : 0<t) (ht₁ : t≤1) : y+t • (z-y)∈Z∩C := by
    let T : Set ℂ := (fun t : ℝ => y+t • (z-y)) '' Ioc 0 1
    have hT : IsPreconnected T := isPreconnected_Ioc.image _ (by fun_prop)
    have hzT : z∈T := ⟨1,⟨zero_lt_one,le_rfl⟩,by simp⟩
    have hTL : T⊆Lᶜ := by
      rintro b ⟨s,hs,rfl⟩ hb
      rw [hL] at hb
      exact hzL (hL ▸ (hstable z hzball s hs.1 hs.2).mp hb)
    exact ⟨hT.subset_connectedComponentIn hzT hTL ⟨t,⟨ht,ht₁⟩,rfl⟩,hrad z hzC t ht ht₁⟩
  let V := U\G
  have hV : IsOpen V := hU.sdiff (isClosed_iUnion_of_finite fun i => (F i).compact_range.isClosed)
  have hzV : z∈V := ⟨hzU,fun h => hzL (Or.inr h)⟩
  have hVL : V⊆Lᶜ := by
    rintro b ⟨hbU,hbG⟩ (hbK|hbG')
    · exact hUK hbU hbK
    · exact hbG hbG'
  have hcomp : connectedComponentIn V z=Z := by
    apply subset_antisymm (connectedComponentIn_mono z hVL)
    apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzL)
    intro b hb
    exact ⟨hZU hb,fun hbG => connectedComponentIn_subset _ _ hb (Or.inr hbG)⟩
  have haccess : ∃ w : ℂ, ∀ t : ℝ,0<t → t≤1 → x+t • (w-x)∈Z := by
    by_cases hn : Nonempty ι
    · let _ : Nonempty ι := hn
      let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
      let _ : DiscreteTopology (ConnectedComponents V) := inferInstance
      have hxcl := tame_star_center_incident_weak F hF Q hQi hU isPreconnected_connectedComponentIn
        x hx h₀ h₁ hFU ConnectedComponents.continuous_coe
        (ConnectedComponents.mk (⟨z,hzV⟩ : V)) ⟨z,hzV,rfl⟩
      change x∈closure (region V ConnectedComponents.mk (ConnectedComponents.mk (⟨z,hzV⟩ : V))) at hxcl
      rw [component_region_eq,hcomp] at hxcl
      have hxG : x∈G := by
        obtain ⟨i⟩ := hn
        exact mem_iUnion.mpr ⟨i,0,h₀ i⟩
      have hxL : x∈⋃ p∈P∪R,segment ℝ p.1 p.2 := hL ▸ Or.inr hxG
      change x∈closure (connectedComponentIn Lᶜ z) at hxcl
      rw [hL] at hxcl
      obtain ⟨w,_,hw⟩ := component_radial_access (P∪R) hxL hxcl
      exact ⟨w,fun t ht ht₁ => by simpa only [←hL] using hw t ht ht₁⟩
    · have hGe : G=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨i,_⟩ := mem_iUnion.mp hb
        exact hn ⟨i⟩
      have hUL : U⊆Lᶜ := by simpa only [L,hGe,union_empty] using hUK
      have hxZ : x∈Z := isPreconnected_connectedComponentIn.subset_connectedComponentIn hzU hUL hx
      exact ⟨x,fun t _ _ => by simpa only [sub_self,smul_zero,add_zero] using hxZ⟩
  obtain ⟨w,hw⟩ := haccess
  obtain ⟨c,hc₀,hc₁,hcS,hcZ,hce⟩ := arc_with_terminal_germ hLc.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hxy (fun h => hyU (hZU h)) hw hzrad
  have hcV (t : I) (ht₀ : t≠0) (ht₁ : t≠1) : c t∈V := by
    have hh : c t∈Z := hcZ t ht₀ ht₁
    rw [←hcomp] at hh
    exact connectedComponentIn_subset _ _ hh
  refine ⟨c,hc₀,hc₁,hcS,?_,?_,hce⟩
  · rintro b ⟨t,ht,rfl⟩
    exact (hcV t ht.1.ne' ht.2.ne).1
  · intro i s t he
    have hs : s=0 ∨ s=1 := by
      by_contra hn
      exact (hcV s (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))).2
        (mem_iUnion.mpr ⟨i,t,he.symm⟩)
    refine ⟨hs,?_⟩
    rcases hs with rfl|rfl
    · exact Or.inl ((F i).injective (he.symm.trans (hc₀.trans (h₀ i).symm)))
    · by_contra hn
      have htU := hFU i ⟨t,⟨lt_of_le_of_ne (show (0:I) ≤ t from t.property.1)
        (fun h => hn (Or.inl h.symm)),lt_of_le_of_ne (le_one t) (fun h => hn (Or.inr h))⟩,rfl⟩
      exact hyU ((he.symm.trans hc₁) ▸ htU)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonPolygonal

theorem finite_prescribed_star (P : Finset (ℂ × ℂ)) {a x : ℂ}
    (hx : x∈connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (n : ℕ) (y : Fin n → ℂ) (C : Fin n → Set ℂ)
    (hy : ∀ i,y i∈⋃ p∈P,segment ℝ p.1 p.2)
    (hC : ∀ i,IsOpen (C i)) (hyC : ∀ i,y i∈closure (C i))
    (hCU : ∀ i,C i⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a)
    (hrad : ∀ i,∀ z∈C i,∀ t : ℝ,0<t → t≤1 → y i+t • (z-y i)∈C i) :
    ∃ F : Fin n → Arc ℂ,
      Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
      (∀ i,F i 0=x) ∧ (∀ i,F i 1=y i) ∧ (∀ i,FiniteSupport (range (F i))) ∧
      (∀ i,F i '' Ioo (0:I) 1⊆connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a) ∧
      ∀ i,∃ ε : ℝ,0<ε ∧ range (F i)∩ball (y i) ε⊆insert (y i) (C i) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,?_,?_,?_,?_,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨F,hF,h₀,h₁,hS,hFU,hgerm⟩ := ih (fun i => y i.succ) (fun i => C i.succ)
      (fun i => hy i.succ) (fun i => hC i.succ) (fun i => hyC i.succ)
      (fun i => hCU i.succ) (fun i => hrad i.succ)
    have h₁' (i : Fin n) : F i 1∉connectedComponentIn (⋃ p∈P,segment ℝ p.1 p.2)ᶜ a := by
      intro h
      exact connectedComponentIn_subset _ _ h (h₁ i ▸ hy i.succ)
    obtain ⟨c,hc₀,hc₁,hcS,hcU,hcF,hce⟩ := extend_star_in_sector P hx (hy 0) F hF hS h₀ h₁'
      hFU (C 0) (hC 0) (hyC 0) (hCU 0) (hrad 0)
    let F' : Fin (n+1) → Arc ℂ := Fin.cases c F
    refine ⟨F',?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact fun h => (h rfl).elim
        · intro _ s t he
          exact hcF j s t he
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ s t he
          exact (hcF i t s he.symm).symm
        · intro h s t he
          exact hF (fun h' => h (congrArg Fin.succ h')) s t he
    · exact Fin.cases hc₀ h₀
    · exact Fin.cases hc₁ h₁
    · exact Fin.cases hcS hS
    · exact Fin.cases hcU hFU
    · exact Fin.cases hce hgerm
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPolygonal

variable {X : Type*} [TopologicalSpace X]

def halfParam : I := ⟨1/2,by constructor <;> norm_num⟩
lemma zero_lt_halfParam : (0:I)<halfParam := by change (0:ℝ)<1/2; norm_num
lemma halfParam_lt_one : halfParam<(1:I) := by change (1/2:ℝ)<1; norm_num

def bisect (a : Arc X) : Bool → Arc X
  | false => a.subarc 0 halfParam zero_lt_halfParam.ne
  | true => a.subarc halfParam 1 halfParam_lt_one.ne

def bisectParam : Bool → I → I
  | false => Icc.convexComb 0 halfParam
  | true => Icc.convexComb halfParam 1

lemma bisect_apply (a : Arc X) (b : Bool) (t : I) : a.bisect b t=a (bisectParam b t) := by
  cases b <;> rfl
lemma bisect_param_endpoint (b : Bool) {t : I}
    (ht : bisectParam b t=0 ∨ bisectParam b t=1) : t=0 ∨ t=1 := by
  cases b
  · exact subarc_parameter_endpoint zero_lt_halfParam ht
  · exact subarc_parameter_endpoint halfParam_lt_one ht
lemma bisect_false_ne_one (t : I) : bisectParam false t≠1 := by
  exact ne_of_lt ((Icc.convexComb_le zero_lt_halfParam.le t).trans_lt halfParam_lt_one)
lemma bisect_true_ne_zero (t : I) : bisectParam true t≠0 := by
  exact ne_of_gt (zero_lt_halfParam.trans_le (Icc.le_convexComb halfParam_lt_one.le t))
lemma bisect_same_param {s t : I} (h : bisectParam false s=bisectParam true t) :
    s=1 ∧ t=0 := by
  have hf := Icc.convexComb_le zero_lt_halfParam.le s
  have ht := Icc.le_convexComb halfParam_lt_one.le t
  have he : bisectParam false s=halfParam := le_antisymm hf (h.symm ▸ ht)
  constructor
  · exact convexComb_injective zero_lt_halfParam (he.trans (Icc.convexComb_one _ _).symm)
  · exact convexComb_injective halfParam_lt_one ((h.symm.trans he).trans (Icc.convexComb_zero _ _).symm)

lemma bisect_compatible (a : Arc X) : Compatible (a.bisect false) (a.bisect true) := by
  constructor
  · intro s t he
    obtain ⟨hs,ht⟩ := bisect_same_param (a.injective he)
    exact ⟨Or.inr hs,Or.inl ht⟩
  · rintro z ⟨⟨s,rfl⟩,⟨t,ht⟩⟩ w ⟨⟨u,rfl⟩,⟨v,hv⟩⟩
    have hs := (bisect_same_param (a.injective ht.symm)).1
    have hu := (bisect_same_param (a.injective hv.symm)).1
    rw [hs,hu]

lemma bisect_range (a : Arc X) : (⋃ b,range (a.bisect b))=range a := by
  apply subset_antisymm
  · intro z hz
    obtain ⟨b,t,rfl⟩ := mem_iUnion.mp hz
    exact ⟨bisectParam b t,(bisect_apply a b t).symm⟩
  · rintro z ⟨t,rfl⟩
    by_cases ht : t≤halfParam
    · apply mem_iUnion.mpr
      refine ⟨false,sliceParam zero_lt_halfParam t ⟨nonneg t,ht⟩,?_⟩
      change a (Icc.convexComb 0 halfParam _) = a t
      congr 1
      apply Subtype.ext
      norm_num [Icc.coe_convexComb,sliceParam,halfParam]
    · apply mem_iUnion.mpr
      refine ⟨true,sliceParam halfParam_lt_one t ⟨(not_le.mp ht).le,le_one t⟩,?_⟩
      change a (Icc.convexComb halfParam 1 _) = a t
      congr 1
      apply Subtype.ext
      norm_num [Icc.coe_convexComb,sliceParam,halfParam]
      ring

lemma weak_compatible_bisect {a b : Arc X}
    (h : ∀ s t : I,a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) (i j : Bool) :
    Compatible (a.bisect i) (b.bisect j) := by
  constructor
  · intro s t he
    rw [bisect_apply,bisect_apply] at he
    obtain ⟨hs,ht⟩ := h _ _ he
    exact ⟨bisect_param_endpoint i hs,bisect_param_endpoint j ht⟩
  · rintro z ⟨⟨s,rfl⟩,⟨t,ht⟩⟩ w ⟨⟨u,rfl⟩,⟨v,hv⟩⟩
    rw [bisect_apply,bisect_apply] at ht hv
    obtain ⟨hs,_⟩ := h _ _ ht.symm
    obtain ⟨hu,_⟩ := h _ _ hv.symm
    rw [bisect_apply,bisect_apply]
    cases i
    · exact congrArg a ((hs.resolve_right (bisect_false_ne_one s)).trans
        (hu.resolve_right (bisect_false_ne_one u)).symm)
    · exact congrArg a ((hs.resolve_left (bisect_true_ne_zero s)).trans
        (hu.resolve_left (bisect_true_ne_zero u)).symm)

theorem bisected_weak_family {ι : Type*} (F : ι → Arc X)
    (hF : Pairwise (fun i j => ∀ s t : I,F i s=F j t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))) :
    Pairwise (fun p q : ι×Bool => Compatible ((F p.1).bisect p.2) ((F q.1).bisect q.2)) := by
  intro ⟨i,b⟩ ⟨j,c⟩ hne
  by_cases hij : i=j
  · subst j
    have hbc : b≠c := fun he => hne (he ▸ rfl)
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact bisect_compatible (F i)
    · exact (bisect_compatible (F i)).symm
    · exact (hbc rfl).elim
  · exact weak_compatible_bisect (hF hij) b c

lemma bisected_family_range {ι : Type*} (F : ι → Arc X) :
    (⋃ p : ι×Bool,range ((F p.1).bisect p.2))=⋃ i,range (F i) := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨i,b⟩,hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i,by rw [←bisect_range (F i)]; exact mem_iUnion.mpr ⟨b,hi⟩⟩
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    rw [←bisect_range (F i)] at hi
    obtain ⟨b,hb⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨(i,b),hb⟩

lemma finiteSupport_bisect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : Arc E} (ha : FiniteSupport (range a)) (b : Bool) : FiniteSupport (range (a.bisect b)) := by
  obtain ⟨P,hP⟩ := ha
  refine ⟨P,?_⟩
  cases b
  · exact (subarc_range_subset a 0 halfParam zero_lt_halfParam.ne).trans hP
  · exact (subarc_range_subset a halfParam 1 halfParam_lt_one.ne).trans hP
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Metric Topology CannonPolygonal

lemma tame_initial_window (P : Finset (ℂ × ℂ)) (a : Arc ℂ)
    (hP : range a⊆⋃ p∈P,segment ℝ p.1 p.2) :
    ∃ q : I,0<q ∧ ∃ ε : ℝ,0<ε ∧ range a∩ball (a 0) ε⊆segment ℝ (a 0) (a q) := by
  classical
  obtain ⟨Q,hQ₀,hQ₁,hQ⟩ := finite_segment_arc_subdivision P a hP
  let R := Q.filter (fun t => (0:I)<t)
  have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨hQ₁,zero_lt_one⟩⟩
  let q := R.min' hR
  have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have hc : Consecutive Q 0 q := ⟨hQ₀,hq.1,hq.2,by
    intro t ht h₀ htq
    exact htq.not_ge (Finset.min'_le R t (Finset.mem_filter.mpr ⟨ht,h₀⟩))⟩
  have hseg := hQ ⟨(0,q),(mem_segments Q 0 q).mpr hc⟩
  rw [subdivArc_range_eq] at hseg
  have hcl : IsClosed (a '' Icc q (1:I)) := (isCompact_Icc.image a.continuous).isClosed
  have hnot : a 0∉a '' Icc q (1:I) := by
    rintro ⟨t,ht,he⟩
    exact hq.2.not_ge (a.injective he ▸ ht.1)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl (a 0) hnot
  refine ⟨q,hq.2,ε,hε,?_⟩
  rintro z ⟨⟨t,rfl⟩,htε⟩
  rw [←hseg]
  refine ⟨t,⟨nonneg t,?_⟩,rfl⟩
  exact le_of_not_gt fun hqt => hball htε ⟨t,⟨hqt.le,le_one t⟩,rfl⟩

def transverse (u : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((ContinuousLinearMap.mul ℝ ℂ) (star u))
@[simp] lemma transverse_apply (u z : ℂ) : transverse u z=(star u*z).im := rfl
@[simp] lemma transverse_self (u : ℂ) : transverse u u=0 := by
  simp [transverse_apply,Complex.mul_im]
  ring

lemma transverse_surjective {u : ℂ} (hu : u≠0) : Function.Surjective (transverse u) := by
  intro r
  refine ⟨(star u)⁻¹*((r:ℂ)*Complex.I),?_⟩
  rw [transverse_apply,←mul_assoc,mul_inv_cancel₀ (star_ne_zero.mpr hu),one_mul]
  simp

lemma transverse_segment {x y z : ℂ} (hz : z∈segment ℝ x y) :
    transverse (y-x) (z-x)=0 := by
  rw [segment_eq_image'] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  simp only [add_sub_cancel_left,map_smul,transverse_self,smul_zero]

lemma tame_endpoint_transverse (P : Finset (ℂ × ℂ)) (a : Arc ℂ)
    (hP : range a⊆⋃ p∈P,segment ℝ p.1 p.2) {x : ℂ} (hx : x=a 0 ∨ x=a 1) :
    ∃ L : ℂ →L[ℝ] ℝ,Function.Surjective L ∧ ∃ ε : ℝ,0<ε ∧
      ∀ z∈range a∩ball x ε,L (z-x)=0 := by
  have hz (b : Arc ℂ) (hb : range b⊆⋃ p∈P,segment ℝ p.1 p.2) :
      ∃ L : ℂ →L[ℝ] ℝ,Function.Surjective L ∧ ∃ ε : ℝ,0<ε ∧
        ∀ z∈range b∩ball (b 0) ε,L (z-b 0)=0 := by
    obtain ⟨q,hq,ε,hε,hs⟩ := tame_initial_window P b hb
    refine ⟨transverse (b q-b 0),transverse_surjective (sub_ne_zero.mpr (b.injective.ne hq.ne')),
      ε,hε,fun z hz => transverse_segment (hs hz)⟩
  rcases hx with rfl|rfl
  · exact hz a hP
  · simpa only [reverse_range,reverse_zero] using hz a.reverse (by simpa only [reverse_range] using hP)

theorem tame_vertex_lines {ι : Type*} [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (P : Finset (ℂ × ℂ)) (hP : ∀ i,range (F i)⊆⋃ p∈P,segment ℝ p.1 p.2)
    {x : ℂ} (hx : Vertex F x) :
    ∃ L : {i // x∈range (F i)} → (ℂ →L[ℝ] ℝ),
      (∀ i,Function.Surjective (L i)) ∧ ∃ ε : ℝ,0<ε ∧
        ∀ z∈(⋃ i,range (F i))∩ball x ε,∃ i,L i (z-x)=0 := by
  classical
  have hend (i : {i // x∈range (F i)}) : x=F i.val 0 ∨ x=F i.val 1 := by
    obtain ⟨t,ht⟩ := i.property
    by_cases ht₀ : t=0
    · exact Or.inl (ht₀ ▸ ht.symm)
    by_cases ht₁ : t=1
    · exact Or.inr (ht₁ ▸ ht.symm)
    exact (interior_not_vertex F hF i.val
      (lt_of_le_of_ne (nonneg t) (Ne.symm ht₀))
      (lt_of_le_of_ne (le_one t) ht₁) (ht.symm ▸ hx)).elim
  choose L hL ε hε hline using fun i : {i // x∈range (F i)} =>
    tame_endpoint_transverse P (F i.val) (hP i.val) (hend i)
  let K := ⋃ i : {i // x∉range (F i)},range (F i.val)
  have hK : IsClosed K := isClosed_iUnion_of_finite fun i => (F i.val).compact_range.isClosed
  have hxK : x∉K := by
    intro hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact i.property hi
  have hW : IsOpen (Kᶜ∩⋂ i,ball x (ε i)) :=
    hK.isOpen_compl.inter (isOpen_iInter_of_finite fun _ => isOpen_ball)
  have hxW : x∈Kᶜ∩⋂ i,ball x (ε i) := ⟨hxK,mem_iInter.mpr fun i => mem_ball_self (hε i)⟩
  obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW x hxW
  refine ⟨L,hL,δ,hδ,?_⟩
  rintro z ⟨hzF,hzδ⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp hzF
  have hxi : x∈range (F i) := by
    by_contra h
    exact (hδW hzδ).1 (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
  exact ⟨⟨i,hxi⟩,hline ⟨i,hxi⟩ z ⟨hi,mem_iInter.mp (hδW hzδ).2 ⟨i,hxi⟩⟩⟩
end CannonEmbeddedArc.Arc

namespace CannonSectors
open Set Metric Topology CannonPolygonal CannonSegmentCones

variable {ι : Type*}

def sector (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ) (b : ι → Bool) : Set ℂ :=
  ball x r∩⋂ i,if b i then {z | 0<L i (z-x)} else {z | L i (z-x)<0}

lemma sector_open [Finite ι] (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ) (b : ι → Bool) :
    IsOpen (sector L x r b) := by
  apply isOpen_ball.inter
  apply isOpen_iInter_of_finite
  intro i
  split
  · exact isOpen_lt continuous_const ((L i).continuous.comp (by fun_prop))
  · exact isOpen_lt ((L i).continuous.comp (by fun_prop)) continuous_const

lemma sector_convex [Finite ι] (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ) (b : ι → Bool) :
    Convex ℝ (sector L x r b) := by
  apply (convex_ball x r).inter
  apply convex_iInter
  intro i
  have he (u v : ℂ) (α β : ℝ) (hαβ : α+β=1) :
      α • u+β • v-x=α • (u-x)+β • (v-x) := by
    rw [smul_sub,smul_sub]
    have hh : α • x+β • x=x := by rw [←add_smul,hαβ,one_smul]
    calc
      α • u+β • v-x=α • u+β • v-(α • x+β • x) := by rw [hh]
      _=α • u-α • x+(β • v-β • x) := by abel
  split
  · intro u hu v hv α β hα hβ hαβ
    change 0<L i (α • u+β • v-x)
    rw [he u v α β hαβ,map_add,map_smul,map_smul]
    exact (convex_Ioi (0:ℝ)) hu hv hα hβ hαβ
  · intro u hu v hv α β hα hβ hαβ
    change L i (α • u+β • v-x)<0
    rw [he u v α β hαβ,map_add,map_smul,map_smul]
    exact (convex_Iio (0:ℝ)) hu hv hα hβ hαβ

lemma sector_radial [Finite ι] (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ) (b : ι → Bool)
    {z : ℂ} (hz : z∈sector L x r b) {t : ℝ} (ht : 0<t) (ht₁ : t≤1) :
    x+t • (z-x)∈sector L x r b := by
  refine ⟨radial_mem_ball hz.1 ht.le ht₁,mem_iInter.mpr fun i => ?_⟩
  have hi := mem_iInter.mp hz.2 i
  have he : x+t • (z-x)-x=t • (z-x) := by abel
  cases hb : b i <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true,mem_ofPred_eq] at hi ⊢
  · simpa only [he,map_smul,smul_eq_mul] using mul_neg_of_pos_of_neg ht hi
  · simpa only [he,map_smul,smul_eq_mul] using mul_pos ht hi

lemma radial_vertex_closure {C : Set ℂ} {x : ℂ} (hne : C.Nonempty)
    (hrad : ∀ z∈C,∀ t : ℝ,0<t → t≤1 → x+t • (z-x)∈C) : x∈closure C := by
  obtain ⟨z,hz⟩ := hne
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min (1/2:ℝ) (ε/(2*(dist z x+1)))
  have hd : 0<2*(dist z x+1) := by positivity
  have ht : 0<t := lt_min (by norm_num) (div_pos hε hd)
  have ht₁ : t≤1 := (min_le_left ..).trans (by norm_num)
  have htd : t*(2*(dist z x+1))≤ε := (le_div_iff₀ hd).mp (min_le_right ..)
  refine ⟨x+t • (z-x),hrad z hz t ht ht₁,?_⟩
  rw [dist_comm,radial_dist x z ht.le]
  nlinarith [dist_nonneg (x:=z) (y:=x)]

lemma sector_vertex_closure [Finite ι] (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ) (b : ι → Bool)
    (hne : (sector L x r b).Nonempty) : x∈closure (sector L x r b) :=
  radial_vertex_closure hne fun _ hz _ ht ht₁ => sector_radial L x r b hz ht ht₁

lemma sector_in_complement [Finite ι] {K : Set ℂ} (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ)
    (hcover : ∀ z∈K∩ball x r,∃ i,L i (z-x)=0) (b : ι → Bool) :
    sector L x r b⊆Kᶜ := by
  rintro z ⟨hzr,hzL⟩ hzK
  obtain ⟨i,hi⟩ := hcover z ⟨hzK,hzr⟩
  have hs := mem_iInter.mp hzL i
  split at hs <;> simp_all <;> linarith

lemma transverse_complement_dense [Finite ι] (L : ι → ℂ →L[ℝ] ℝ)
    (hL : ∀ i,Function.Surjective (L i)) (x : ℂ) :
    Dense (⋂ i,{z | L i (z-x)≠0}) := by
  apply dense_iInter_of_isOpen
  · intro i
    exact isOpen_ne_fun ((L i).continuous.comp (by fun_prop)) continuous_const
  · intro i
    exact (dense_compl_singleton (0:ℝ)).preimage
      ((L i).isOpenMap (hL i) |>.comp (Homeomorph.addRight (-x)).isOpenMap)

lemma mem_some_sector [Finite ι] (L : ι → ℂ →L[ℝ] ℝ) (x : ℂ) (r : ℝ) {z : ℂ}
    (hzr : z∈ball x r) (hL : ∀ i,L i (z-x)≠0) :
    ∃ b : ι → Bool,z∈sector L x r b := by
  classical
  refine ⟨fun i => decide (0<L i (z-x)),hzr,mem_iInter.mpr fun i => ?_⟩
  by_cases hi : 0<L i (z-x)
  · simp only [hi,decide_true,ite_true,mem_ofPred_eq]
  · simpa only [hi,decide_false,Bool.false_eq_true,ite_false,mem_ofPred_eq] using
      lt_of_le_of_ne (le_of_not_gt hi) (hL i)

theorem face_contains_sector [Finite ι] {K : Set ℂ} (hK : IsClosed K)
    (L : ι → ℂ →L[ℝ] ℝ) (hL : ∀ i,Function.Surjective (L i))
    {x : ℂ} {r : ℝ} (hr : 0<r)
    (hcover : ∀ z∈K∩ball x r,∃ i,L i (z-x)=0)
    {a : ℂ} (hx : x∈closure (connectedComponentIn Kᶜ a)) :
    ∃ b : ι → Bool,(sector L x r b).Nonempty ∧
      sector L x r b⊆connectedComponentIn Kᶜ a ∧ x∈closure (sector L x r b) := by
  let U := connectedComponentIn Kᶜ a
  have hU : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hmeet : (U∩ball x r).Nonempty := by
    obtain ⟨z,hzr,hzU⟩ := mem_closure_iff.mp hx (ball x r) isOpen_ball (mem_ball_self hr)
    exact ⟨z,hzU,hzr⟩
  obtain ⟨z,hz,hzd⟩ := (transverse_complement_dense L hL x).inter_open_nonempty
    (U∩ball x r) (hU.inter isOpen_ball) hmeet
  obtain ⟨b,hb⟩ := mem_some_sector L x r hz.2 (mem_iInter.mp hzd)
  have hC := sector_in_complement L x r hcover b
  have hCZ : sector L x r b⊆connectedComponentIn Kᶜ z :=
    (sector_convex L x r b).isPreconnected.subset_connectedComponentIn hb hC
  have he : connectedComponentIn Kᶜ z=U := (connectedComponentIn_eq hz.1).symm
  have hCU : sector L x r b⊆U := by simpa only [he] using hCZ
  exact ⟨b,⟨z,hb⟩,hCU,sector_vertex_closure L x r b ⟨z,hb⟩⟩
end CannonSectors

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
