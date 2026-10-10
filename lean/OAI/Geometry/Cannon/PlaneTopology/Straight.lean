import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Consecutive

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
namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsStraight (a : Arc E) : Prop :=
  ∃ f : ℝ →ᵃ[ℝ] E, ∀ t : I, a t=f (t:ℝ)

def lineArc (a b : E) (hab : a≠b) : Arc E :=
  ⟨(Path.segment a b).toContinuousMap,Path.segment_injective_of_ne hab⟩
@[simp] lemma lineArc_zero (a b : E) (hab : a≠b) : lineArc a b hab 0=a := (Path.segment a b).source
@[simp] lemma lineArc_one (a b : E) (hab : a≠b) : lineArc a b hab 1=b := (Path.segment a b).target
lemma lineArc_straight (a b : E) (hab : a≠b) : IsStraight (lineArc a b hab) :=
  ⟨AffineMap.lineMap a b,Path.segment_apply a b⟩
lemma lineArc_range (a b : E) (hab : a≠b) :
    range (lineArc a b hab)=segment ℝ a b := Path.range_segment a b

lemma IsStraight.range_eq {a : Arc E} (ha : IsStraight a) :
    range a=segment ℝ (a 0) (a 1) := by
  obtain ⟨f,hf⟩ := ha
  have he : range a=f '' Set.Icc (0:ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,(hf t).symm⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,hf ⟨t,ht⟩⟩
  rw [he,←segment_eq_Icc (show (0:ℝ)≤1 by norm_num),image_segment]
  rw [hf 0,hf 1]
  rfl

lemma IsStraight.subarc {a : Arc E} (ha : IsStraight a) (u v : I) (huv : u≠v) :
    IsStraight (a.subarc u v huv) := by
  obtain ⟨f,hf⟩ := ha
  refine ⟨f.comp (AffineMap.lineMap (u:ℝ) (v:ℝ)),fun t => ?_⟩
  change a (Icc.convexComb u v t)=f (AffineMap.lineMap (u:ℝ) (v:ℝ) (t:ℝ))
  rw [hf]
  congr 1
  simp only [Icc.coe_convexComb,AffineMap.lineMap_apply_module,smul_eq_mul]

lemma IsStraight.preimage_convex {a : Arc E} (ha : IsStraight a)
    {S : Set E} (hS : Convex ℝ S) : OrdConnected (a ⁻¹' S) := by
  obtain ⟨f,hf⟩ := ha
  refine ⟨fun u hu v hv t ht => ?_⟩
  have htseg : (t:ℝ)∈segment ℝ (u:ℝ) (v:ℝ) := by
    rw [segment_eq_Icc (show (u:ℝ)≤v from ht.1.trans ht.2)]
    exact ht
  have hft : f (t:ℝ)∈segment ℝ (f u) (f v) := by
    rw [←image_segment]
    exact ⟨t,htseg,rfl⟩
  rw [←hf u,←hf v] at hft
  change a t∈S
  rw [hf]
  exact hS.segment_subset hu hv hft

theorem insert_straight_arrangement {ι : Type*} [Fintype ι]
    (F : ι → Arc E) (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (hFs : ∀ i, IsStraight (F i)) (a : Arc E) (ha : IsStraight a) :
    ∃ n : ℕ, ∃ B : Fin n → Arc E,
      Pairwise (fun i j => Compatible (B i) (B j)) ∧
      (∀ i, IsStraight (B i)) ∧ (⋃ i, range (B i))=(⋃ i, range (F i))∪range a := by
  classical
  have hc (i : ι) : OrdConnected (a ⁻¹' range (F i)) := by
    apply ha.preimage_convex
    rw [(hFs i).range_eq]
    exact convex_segment ..
  obtain ⟨P,hP₀,hP₁,_,hP⟩ := finite_breakpoints F Finset.univ a (fun i _ => hc i)
  choose Q hQ₀ hQ₁ hQc hQ using fun i => old_breakpoints a (F i) P
  let A : Unit → Arc E := fun _ => a
  let PP : Unit → Finset I := fun _ => P
  have hA : Pairwise (fun i j => Disjoint (range (A i)) (range (A j))) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hinterval : ∀ i e, (A i ⁻¹' range (F e))=∅ ∨
      ∃ u∈PP i, ∃ v∈PP i, u≤v ∧ A i ⁻¹' range (F e)=Icc u v :=
    fun _ e => hP e (Finset.mem_univ e)
  have hmark : ∀ i e t, F e t∈A i '' (PP i:Set I) → t∈Q e := fun _ e => hQ e
  let R := refinementArc F A PP Q
  have hRc : Pairwise (fun z w => Compatible (R z) (R w)) :=
    refinement_compatible F A PP Q hF hA hinterval hmark
  have hRs (z : RefinementIndex F A PP Q) : IsStraight (R z) := by
    rcases z with ⟨i,z⟩|⟨i,z⟩
    · exact (hFs i).subarc _ _ (segment_consecutive (Q i) z).2.2.1.ne
    · exact ha.subarc _ _ (segment_consecutive (PP i) z.val).2.2.1.ne
  have hcover : (⋃ z, range (R z))=(⋃ i, range (F i))∪range a := by
    have hh := (refinement_cover F A PP Q (fun _ => hP₀) (fun _ => hP₁) hQ₀ hQ₁).symm
    simpa only [A,iUnion_const] using hh
  let e := Fintype.equivFin (RefinementIndex F A PP Q)
  refine ⟨_,R ∘ e.symm,?_,fun i => hRs (e.symm i),?_⟩
  · intro i j hij
    exact hRc (fun h => hij (e.symm.injective h))
  · rw [←hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e.symm i,hi⟩
    · intro hx
      obtain ⟨z,hz⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e z,by simpa using hz⟩

theorem straight_arrangement (P : Finset (E×E)) (hne : ∀ p∈P, p.1≠p.2) :
    ∃ n : ℕ, ∃ F : Fin n → Arc E,
      Pairwise (fun i j => Compatible (F i) (F j)) ∧
      (∀ i, IsStraight (F i)) ∧ (⋃ i, range (F i))=⋃ p∈P, segment ℝ p.1 p.2 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨0,Fin.elim0,?_,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · simp
  | @insert p P hp ih =>
    obtain ⟨n,F,hFc,hFs,hFr⟩ := ih (fun q hq => hne q (Finset.mem_insert_of_mem hq))
    have hn := hne p (Finset.mem_insert_self p P)
    obtain ⟨m,B,hBc,hBs,hBr⟩ := insert_straight_arrangement F hFc hFs
      (lineArc p.1 p.2 hn) (lineArc_straight p.1 p.2 hn)
    refine ⟨m,B,hBc,hBs,?_⟩
    rw [hBr,hFr,lineArc_range]
    simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
    exact union_comm ..
end Arc
end CannonEmbeddedArc

noncomputable section
open Set unitInterval

namespace CannonTame
variable {X : Type*} [TopologicalSpace X]

lemma connected_in_finite_closed_cover {ι : Type*} [Finite ι]
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i))
    {C : Set X} (hC : IsConnected C) (hcov : C⊆⋃ i, F i)
    (hdisj : ∀ i j, i≠j → C∩(F i∩F j)=∅) :
    ∃ i, C⊆F i := by
  classical
  obtain ⟨x,hx⟩ := hC.nonempty
  obtain ⟨i,hxi⟩ := mem_iUnion.mp (hcov hx)
  refine ⟨i,?_⟩
  let W := ⋃ j : {j : ι // j≠i}, F j.val
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun j => hF j.val)
  have hxW : x∉W := by
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    have hh : x∈C∩(F j.val∩F i) := ⟨hx,hj,hxi⟩
    rw [hdisj j.val i j.property] at hh
    exact hh
  intro y hy
  by_contra hyi
  have hcover : C⊆Wᶜ∪(F i)ᶜ := by
    intro z hz
    by_cases hzi : z∈F i
    · left
      intro hzW
      obtain ⟨j,hj⟩ := mem_iUnion.mp hzW
      have hh : z∈C∩(F j.val∩F i) := ⟨hz,hj,hzi⟩
      rw [hdisj j.val i j.property] at hh
      exact hh
    · exact Or.inr hzi
  obtain ⟨z,hz,hzW,hzi⟩ := hC.isPreconnected _ _ hW.isOpen_compl (hF i).isOpen_compl
    hcover ⟨x,hx,hxW⟩ ⟨y,hy,hyi⟩
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov hz)
  by_cases hji : j=i
  · exact hzi (hji ▸ hj)
  · exact hzW (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
end CannonTame

namespace CannonEmbeddedArc.Arc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma IsStraight.image_Icc {a : Arc E} (ha : IsStraight a) {u v : I} (huv : u≤v) :
    a '' Icc u v=segment ℝ (a u) (a v) := by
  obtain ⟨f,hf⟩ := ha
  have he : a '' Icc u v=f '' Icc (u:ℝ) (v:ℝ) := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,(hf t).symm⟩
    · rintro ⟨t,ht,rfl⟩
      let w : I := ⟨t,⟨u.property.1.trans ht.1,ht.2.trans v.property.2⟩⟩
      exact ⟨w,ht,hf w⟩
  rw [he,←segment_eq_Icc (show (u:ℝ)≤v from huv),image_segment,hf u,hf v]

lemma range_eq_segment_of_subset {a b : Arc E} (ha : IsStraight a)
    (hsub : range b⊆range a) : range b=segment ℝ (b 0) (b 1) := by
  let e := (a.continuous.isClosedEmbedding a.injective).isEmbedding.toHomeomorph
  let f : I → range a := fun t => ⟨b t,hsub (mem_range_self t)⟩
  let g : I → I := e.symm ∘ f
  have hfc : Continuous f := b.continuous.subtype_mk _
  have hgc : Continuous g := e.symm.continuous.comp hfc
  have hgf (t : I) : a (g t)=b t := by
    have hh := congrArg Subtype.val (e.apply_symm_apply (f t))
    exact hh
  have hgi : Function.Injective g := by
    intro s t hst
    apply b.injective
    rw [←hgf s,←hgf t,hst]
  have hgr : range b=a '' range g := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨g t,mem_range_self t,hgf t⟩
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨t,(hgf t).symm⟩
  have hc : OrdConnected (range g) := (isPreconnected_range hgc).ordConnected
  rcases hgc.strictMono_of_inj_boundedOrder' hgi with hm|hm
  · have he : range g=Icc (g 0) (g 1) := by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        exact ⟨hm.monotone (unitInterval.nonneg t),hm.monotone (unitInterval.le_one t)⟩
      · exact hc.out (mem_range_self 0) (mem_range_self 1)
    rw [hgr,he,ha.image_Icc (hm.monotone zero_le_one),hgf 0,hgf 1]
  · have he : range g=Icc (g 1) (g 0) := by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        exact ⟨hm.antitone (unitInterval.le_one t),hm.antitone (unitInterval.nonneg t)⟩
      · exact hc.out (mem_range_self 1) (mem_range_self 0)
    rw [hgr,he,ha.image_Icc (hm.antitone zero_le_one),hgf 0,hgf 1,segment_symm]

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
lemma Compatible.congr_endpoints_range {a b c d : Arc X} (hab : Compatible a b)
    (hca : range c=range a) (hdb : range d=range b)
    (hc₀ : c 0=a 0) (hc₁ : c 1=a 1) (hd₀ : d 0=b 0) (hd₁ : d 1=b 1) :
    Compatible c d := by
  constructor
  · intro t s hts
    obtain ⟨u,hu⟩ : c t∈range a := hca ▸ mem_range_self t
    obtain ⟨v,hv⟩ : d s∈range b := hdb ▸ mem_range_self s
    obtain ⟨hua,hvb⟩ := hab.1 u v (hu.trans (hts.trans hv.symm))
    constructor
    · rcases hua with rfl|rfl
      · exact Or.inl (c.injective (hu.symm.trans hc₀.symm))
      · exact Or.inr (c.injective (hu.symm.trans hc₁.symm))
    · rcases hvb with rfl|rfl
      · exact Or.inl (d.injective (hv.symm.trans hd₀.symm))
      · exact Or.inr (d.injective (hv.symm.trans hd₁.symm))
  · rw [hca,hdb]
    exact hab.2

lemma subarc_in_one_edge {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (a : Arc X) (P : Finset I) {p q : I} (hpq : Consecutive P p q)
    (hcov : ∀ t : I, t≠0 → t≠1 →
      a.subarc p q hpq.2.2.1.ne t∈⋃ i, range (F i))
    (hmark : ∀ t, Vertex F (a t) → t∈P) :
    ∃ i, range (a.subarc p q hpq.2.2.1.ne)⊆range (F i) := by
  let b := a.subarc p q hpq.2.2.1.ne
  let C := b '' Ioo (0:I) 1
  have hC : IsConnected C :=
    (isConnected_Ioo (show (0:I)<1 from zero_lt_one)).image b b.continuous.continuousOn
  have hcover : C⊆⋃ i, range (F i) := by
    rintro _ ⟨t,ht,rfl⟩
    exact hcov t (ne_of_gt ht.1) (ne_of_lt ht.2)
  have hdisj (i j : ι) (hij : i≠j) : C∩(range (F i)∩range (F j))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨t,ht,he⟩,⟨u,hu⟩,⟨v,hv⟩⟩
    obtain ⟨hui,_⟩ := (hF hij).1 u v (hu.trans hv.symm)
    have hvtx : Vertex F (b t) := by
      refine ⟨i,?_⟩
      rcases hui with rfl|rfl
      · exact Or.inl (hu.trans he.symm)
      · exact Or.inr (hu.trans he.symm)
    have hm := hmark (Icc.convexComb p q t) hvtx
    rcases hpq.marked_parameter t hm with h|h
    · exact (ne_of_gt ht.1) h
    · exact (ne_of_lt ht.2) h
  obtain ⟨i,hi⟩ := CannonTame.connected_in_finite_closed_cover
    (fun i => range (F i)) (fun i => (F i).compact_range.isClosed) hC hcover hdisj
  refine ⟨i,range_subset_of_interior (F i).compact_range.isClosed b ?_⟩
  intro t ht₀ ht₁
  apply hi
  refine ⟨t,⟨?_,?_⟩,rfl⟩
  · exact lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht₀)
  · exact lt_of_le_of_ne (unitInterval.le_one t) ht₁
end CannonEmbeddedArc.Arc

noncomputable section
namespace CannonEmbeddedArc.Arc
open Set unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem arc_in_arrangement_subdivision {ι : Type*} [Finite ι]
    (F : ι → Arc E) (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (hFs : ∀ i, IsStraight (F i)) (T : Finset E)
    (a : Arc E) (hsub : range a⊆(⋃ i, range (F i))∪(T:Set E)) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧
      ∀ z : segments P, range (subdivArc a P z)=
        segment ℝ (a z.val.1) (a z.val.2) := by
  classical
  let V : Set E := (range (fun i => F i 0)∪range (fun i => F i 1))∪(T:Set E)
  have hV : V.Finite := ((finite_range _).union (finite_range _)).union T.finite_toSet
  have hpre : (a ⁻¹' V).Finite := hV.preimage a.injective.injOn
  let P := insert 0 (insert 1 hpre.toFinset)
  have hmarkV (t : I) (ht : a t∈V) : t∈P :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hpre.mem_toFinset.mpr ht))
  refine ⟨P,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_⟩
  intro z
  have hz := segment_consecutive P z
  have havoid (t : I) (ht₀ : t≠0) (ht₁ : t≠1) :
      subdivArc a P z t∉V := by
    intro hv
    have hmem := hmarkV (Icc.convexComb z.val.1 z.val.2 t) hv
    rcases hz.marked_parameter t hmem with h|h
    · exact ht₀ h
    · exact ht₁ h
  have hcover (t : I) (ht₀ : t≠0) (ht₁ : t≠1) :
      subdivArc a P z t∈⋃ i, range (F i) := by
    rcases hsub (subdivArc_range_subset a P z (mem_range_self t)) with h|h
    · exact h
    · exact (havoid t ht₀ ht₁ (Or.inr h)).elim
  have hmark (t : I) (ht : Vertex F (a t)) : t∈P := by
    apply hmarkV
    obtain ⟨i,hi|hi⟩ := ht
    · exact Or.inl (Or.inl ⟨i,hi⟩)
    · exact Or.inl (Or.inr ⟨i,hi⟩)
  obtain ⟨i,hi⟩ := subarc_in_one_edge F hF a P hz hcover hmark
  have hh := range_eq_segment_of_subset (hFs i) hi
  change range (subdivArc a P z)=segment ℝ
    (subdivArc a P z 0) (subdivArc a P z 1) at hh
  simpa only [subdivArc_zero,subdivArc_one] using hh

theorem finite_segment_arc_subdivision (Q : Finset (E×E)) (a : Arc E)
    (hsub : range a⊆⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧
      ∀ z : segments P, range (subdivArc a P z)=
        segment ℝ (a z.val.1) (a z.val.2) := by
  classical
  let R := Q.filter (fun q => q.1≠q.2)
  obtain ⟨n,F,hFc,hFs,hFr⟩ := straight_arrangement R
    (fun p hp => (Finset.mem_filter.mp hp).2)
  let T := Q.image Prod.fst
  apply arc_in_arrangement_subdivision F hFc hFs T a
  intro x hx
  obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp (hsub hx)
  by_cases hn : q.1=q.2
  · right
    have hxq' : x=q.1 := by simpa only [←hn,segment_same,mem_singleton_iff] using hxq
    exact hxq' ▸ Finset.mem_image_of_mem Prod.fst hq
  · left
    rw [hFr]
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hn⟩,hxq⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval

lemma consecutive_neighbors (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) (ht : t∈P) :
    ∃ p q, Consecutive P p t ∧ Consecutive P t q := by
  classical
  let L := P.filter (· < t)
  let R := P.filter (t < ·)
  have hL : L.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨h₀,ht₀⟩⟩
  have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,ht₁⟩⟩
  let p := L.max' hL
  let q := R.min' hR
  have hp := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
  refine ⟨p,q,⟨hp.1,ht,hp.2,?_⟩,⟨ht,hq.1,hq.2,?_⟩⟩
  · intro z hz hpz hzt
    exact hpz.not_ge (Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz,hzt⟩))
  · intro z hz htz hzq
    exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,htz⟩))

lemma consecutive_refinement {P Q : Finset I} (h₀ : 0∈P) (h₁ : 1∈P)
    (hPQ : P⊆Q) {p q : I} (hpq : Consecutive Q p q) :
    ∃ u v, Consecutive P u v ∧ Icc p q⊆Icc u v := by
  obtain ⟨m,hpm,hmq⟩ := exists_between hpq.2.2.1
  obtain ⟨u,v,huv,hum,hmv⟩ := consecutive_cover P h₀ h₁ m
  have hup : u≤p := by
    by_contra h
    exact hpq.2.2.2 u (hPQ huv.1) (lt_of_not_ge h) (hum.trans_lt hmq)
  have hqv : q≤v := by
    by_contra h
    exact hpq.2.2.2 v (hPQ huv.2.1) (hpm.trans_le hmv) (lt_of_not_ge h)
  exact ⟨u,v,huv,fun _ h => ⟨hup.trans h.1,h.2.trans hqv⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_subarc_image (a : Arc E) {p q u v : I} (hpq : p<q) (huv : u<v)
    (he : a '' Icc p q=segment ℝ (a p) (a q)) (hsub : Icc u v⊆Icc p q) :
    a '' Icc u v=segment ℝ (a u) (a v) := by
  let b := a.subarc u v huv.ne
  have hsub' : range b⊆range (lineArc (a p) (a q) (a.injective.ne hpq.ne)) := by
    rw [lineArc_range,←he]
    exact (subarc_range_eq a huv).subset.trans (image_mono hsub)
  have hh := range_eq_segment_of_subset
    (lineArc_straight (a p) (a q) (a.injective.ne hpq.ne)) hsub'
  change range (a.subarc u v huv.ne)=segment ℝ
    (a.subarc u v huv.ne 0) (a.subarc u v huv.ne 1) at hh
  rw [←subarc_range_eq a huv]
  simpa only [subarc_zero,subarc_one] using hh

lemma straight_subdivision_refines (a : Arc E) {P Q : Finset I} (h₀ : 0∈P) (h₁ : 1∈P)
    (hPQ : P⊆Q) (hP : ∀ z : segments P,
      range (subdivArc a P z)=segment ℝ (a z.val.1) (a z.val.2)) :
    ∀ z : segments Q, range (subdivArc a Q z)=segment ℝ (a z.val.1) (a z.val.2) := by
  intro z
  have hz := segment_consecutive Q z
  obtain ⟨u,v,huv,hsub⟩ := consecutive_refinement h₀ h₁ hPQ hz
  let w : segments P := ⟨(u,v),(mem_segments P u v).mpr huv⟩
  have hw := hP w
  rw [subdivArc_range_eq] at hw ⊢
  exact segment_subarc_image a huv.2.2.1 hz.2.2.1 hw hsub

lemma corner_not_sameRay (a : Arc E) {p t q : I} (hpt : p<t) (htq : t<q)
    (hleft : a '' Icc p t=segment ℝ (a p) (a t))
    (hright : a '' Icc t q=segment ℝ (a t) (a q)) :
    ¬SameRay ℝ (a p-a t) (a q-a t) := by
  intro h
  have hu : a p-a t≠0 := sub_ne_zero.mpr (a.injective.ne hpt.ne)
  have hv : a q-a t≠0 := sub_ne_zero.mpr (a.injective.ne htq.ne.symm)
  obtain ⟨r,hr,he⟩ := h.exists_pos_left hu hv
  by_cases hr₁ : r≤1
  · have hmem : a q∈segment ℝ (a t) (a p) := by
      rw [segment_eq_image']
      exact ⟨r,⟨hr.le,hr₁⟩,by dsimp only; rw [he]; abel⟩
    rw [segment_symm,←hleft] at hmem
    obtain ⟨s,hs,hse⟩ := hmem
    have hsq := a.injective hse
    subst s
    exact htq.not_ge hs.2
  · have hr₁' : 1≤r := (lt_of_not_ge hr₁).le
    have hei : r⁻¹ • (a q-a t)=a p-a t := by
      rw [←he,inv_smul_smul₀ hr.ne']
    have hmem : a p∈segment ℝ (a t) (a q) := by
      rw [segment_eq_image']
      exact ⟨r⁻¹,⟨inv_nonneg.mpr hr.le,inv_le_one_of_one_le₀ hr₁'⟩,by dsimp only; rw [hei]; abel⟩
    rw [←hright] at hmem
    obtain ⟨s,hs,hse⟩ := hmem
    have hsp := a.injective hse
    subst s
    exact hpt.not_ge hs.1

theorem tame_interior_corner (Q : Finset (E×E)) (a : Arc E)
    (hsub : range a⊆⋃ q∈Q, segment ℝ q.1 q.2)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ p q : I, p<t ∧ t<q ∧
      a '' Icc p t=segment ℝ (a p) (a t) ∧
      a '' Icc t q=segment ℝ (a t) (a q) ∧
      ¬SameRay ℝ (a p-a t) (a q-a t) := by
  classical
  obtain ⟨P,hP₀,hP₁,hP⟩ := finite_segment_arc_subdivision Q a hsub
  let R := insert t P
  have hPR : P⊆R := Finset.subset_insert _ _
  obtain ⟨p,q,hpt,htq⟩ := consecutive_neighbors R (hPR hP₀) (hPR hP₁) ht₀ ht₁
    (Finset.mem_insert_self _ _)
  have hR := straight_subdivision_refines a hP₀ hP₁ hPR hP
  have hleft := hR ⟨(p,t),(mem_segments R p t).mpr hpt⟩
  have hright := hR ⟨(t,q),(mem_segments R t q).mpr htq⟩
  rw [subdivArc_range_eq] at hleft hright
  exact ⟨p,q,hpt.2.2.1,htq.2.2.1,hleft,hright,
    corner_not_sameRay a hpt.2.2.1 htq.2.2.1 hleft hright⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem isolate_edge_interior {ι : Type*} [Finite ι] (F : ι → Arc X)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
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
    have hh := (hF j.property.symm).1 t s hs.symm
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
