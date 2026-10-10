import Mathlib

namespace OAI

/-! Embedded arcs and compatible finite subdivisions. -/

section
section
section
noncomputable section
open Set unitInterval Topology

namespace CannonEmbeddedArc

structure Arc (X : Type*) [TopologicalSpace X] where
  map : C(I, X)
  injective : Function.Injective map

variable {X : Type*} [TopologicalSpace X]
instance : CoeFun (Arc X) (fun _ => I → X) := ⟨fun a => a.map⟩

namespace Arc
lemma continuous (a : Arc X) : Continuous a := a.map.continuous
lemma compact_range (a : Arc X) : IsCompact (range a) := isCompact_range a.continuous
lemma endpoints_ne (a : Arc X) : a 0 ≠ a 1 := fun h => by
  have := a.injective h
  exact zero_ne_one this

def path (a : Arc X) : Path (a 0) (a 1) :=
  { toContinuousMap := a.map, source' := rfl, target' := rfl }

@[simp] lemma path_apply (a : Arc X) (t : I) : a.path t = a t := rfl

def subarc (a : Arc X) (u v : I) (huv : u ≠ v) : Arc X where
  map := ⟨fun t => a (Icc.convexComb u v t),
    a.continuous.comp (Icc.continuous_convexComb u v)⟩
  injective := by
    intro s t h
    have hh := congrArg Subtype.val (a.injective h)
    simp only [Icc.coe_convexComb] at hh
    apply Subtype.ext
    have hn : (u : ℝ) ≠ v := fun h => huv (Subtype.ext h)
    have : ((s : ℝ) - t) * ((v : ℝ) - u) = 0 := by nlinarith [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hn.symm))

@[simp] lemma subarc_zero (a : Arc X) (u v : I) (huv : u ≠ v) :
    a.subarc u v huv 0 = a u := by simp [subarc]
@[simp] lemma subarc_one (a : Arc X) (u v : I) (huv : u ≠ v) :
    a.subarc u v huv 1 = a v := by simp [subarc]
lemma subarc_range_subset (a : Arc X) (u v : I) (huv : u ≠ v) :
    range (a.subarc u v huv) ⊆ range a := by
  rintro _ ⟨t,rfl⟩
  exact mem_range_self _

def spliceFun (a b : Arc X) (u v : I) (t : I) : X :=
  if t ≤ u then a t else if t ≤ v then b.path.extend (((t : ℝ)-u)/((v : ℝ)-u)) else a t

lemma spliceFun_left (a b : Arc X) (u v t : I) (ht : t ≤ u) :
    spliceFun a b u v t = a t := by simp [spliceFun,ht]
lemma spliceFun_right (a b : Arc X) {u v t : I} (huv : u < v)
    (hend : b 1 = a v) (ht : v ≤ t) : spliceFun a b u v t = a t := by
  by_cases htv : t = v
  · subst t
    simp [spliceFun,not_le.mpr huv,div_self (sub_ne_zero.mpr (show (v : ℝ) ≠ u from ne_of_gt huv)),hend]
  · have hvt : v < t := lt_of_le_of_ne ht (Ne.symm htv)
    simp [spliceFun,not_le.mpr (huv.trans hvt),not_le.mpr hvt]

lemma continuous_spliceFun (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (hend : b 1 = a v) :
    Continuous (spliceFun a b u v) := by
  have hd : (v : ℝ)-u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
  have hb : Continuous (fun t : I => b.path.extend (((t : ℝ)-u)/((v : ℝ)-u))) :=
    b.path.continuous_extend.comp (by fun_prop)
  unfold spliceFun
  apply a.continuous.if_le
    (hb.if_le a.continuous continuous_id continuous_const ?_)
    continuous_id continuous_const ?_
  · intro t ht
    change t = v at ht
    subst t
    simpa [div_self hd] using hend
  · intro t ht
    change t = u at ht
    subst t
    simp [huv.le,hstart]

def sliceParam {u v : I} (huv : u < v) (t : I) (ht : t ∈ Icc u v) : I :=
  ⟨((t : ℝ)-u)/((v : ℝ)-u), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr (show (u : ℝ) < v from huv)).le
    · apply (div_le_one (sub_pos.mpr (show (u : ℝ)<v from huv))).2
      exact sub_le_sub_right (show (t : ℝ) ≤ v from ht.2) _⟩

lemma spliceFun_middle (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (t : I) (ht : t ∈ Icc u v) :
    spliceFun a b u v t = b (sliceParam huv t ht) := by
  by_cases htu : t ≤ u
  · have he : t=u := le_antisymm htu ht.1
    subst t
    have hs : sliceParam huv u ht=0 := by ext; simp [sliceParam]
    simp [spliceFun,hs,hstart]
  · simp only [spliceFun,htu,ite_false,ht.2,ite_true]
    exact b.path.extend_apply (sliceParam huv t ht).property

lemma spliceFun_outside (a b : Arc X) {u v t : I} (ht : t ∉ Icc u v) :
    spliceFun a b u v t = a t := by
  by_cases htu : t ≤ u
  · exact spliceFun_left a b u v t htu
  · have htv : ¬t ≤ v := fun h => ht ⟨(not_le.mp htu).le,h⟩
    simp [spliceFun,htu,htv]

lemma injective_spliceFun (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (havoid : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    Function.Injective (spliceFun a b u v) := by
  intro s t he
  by_cases hs : s ∈ Icc u v <;> by_cases ht : t ∈ Icc u v
  · rw [spliceFun_middle a b huv hstart s hs,
      spliceFun_middle a b huv hstart t ht] at he
    have h := congrArg Subtype.val (b.injective he)
    simp only [sliceParam] at h
    have hd : (v : ℝ)-u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
    have hst := (div_left_inj' hd).mp h
    apply Subtype.ext
    linarith
  · rw [spliceFun_middle a b huv hstart s hs,spliceFun_outside a b ht] at he
    exact False.elim (havoid t ht ⟨sliceParam huv s hs,he⟩)
  · rw [spliceFun_outside a b hs,spliceFun_middle a b huv hstart t ht] at he
    exact False.elim (havoid s hs ⟨sliceParam huv t ht,he.symm⟩)
  · rw [spliceFun_outside a b hs,spliceFun_outside a b ht] at he
    exact a.injective he

def splice (a b : Arc X) {u v : I} (huv : u < v)
    (hstart : b 0 = a u) (hend : b 1 = a v)
    (havoid : ∀ t : I, t ∉ Icc u v → a t ∉ range b) : Arc X :=
  ⟨⟨spliceFun a b u v,continuous_spliceFun a b huv hstart hend⟩,
    injective_spliceFun a b huv hstart havoid⟩

lemma splice_range_subset (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    range (splice a b huv hs he ha) ⊆ range a ∪ range b := by
  rintro _ ⟨t,rfl⟩
  change spliceFun a b u v t ∈ range a ∪ range b
  by_cases ht : t ∈ Icc u v
  · rw [spliceFun_middle a b huv hs t ht]
    exact Or.inr (mem_range_self _)
  · rw [spliceFun_outside a b ht]
    exact Or.inl (mem_range_self _)

@[simp] lemma splice_zero (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    splice a b huv hs he ha 0 = a 0 :=
  spliceFun_left a b u v 0 (unitInterval.nonneg u)

@[simp] lemma splice_one (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b) :
    splice a b huv hs he ha 1 = a 1 :=
  spliceFun_right a b huv he (unitInterval.le_one v)

lemma sliceParam_interior {u v t : I} (huv : u < v) (ht : t ∈ Ioo u v) :
    0 < sliceParam huv t ⟨ht.1.le,ht.2.le⟩ ∧
    sliceParam huv t ⟨ht.1.le,ht.2.le⟩ < 1 := by
  constructor
  · change 0 < ((t : ℝ)-u)/((v : ℝ)-u)
    exact div_pos (sub_pos.mpr ht.1) (sub_pos.mpr huv)
  · change ((t : ℝ)-u)/((v : ℝ)-u) < 1
    rw [div_lt_one (sub_pos.mpr (show (u : ℝ)<v from huv))]
    exact sub_lt_sub_right (show (t : ℝ)<v from ht.2) _

lemma spliceFun_same_outside_open (a b : Arc X) {u v t : I} (huv : u < v)
    (hend : b 1 = a v) (ht : t ∉ Ioo u v) :
    spliceFun a b u v t = a t := by
  rcases le_or_gt t u with h|h
  · exact spliceFun_left a b u v t h
  · exact spliceFun_right a b huv hend (le_of_not_gt (fun h' => ht ⟨h,h'⟩))

lemma splice_preimage (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b)
    (S : Set X) (hS : ∀ t : I, 0<t → t<1 → b t ∉ S) :
    (splice a b huv hs he ha) ⁻¹' S = (a ⁻¹' S) \ Ioo u v := by
  ext t
  change spliceFun a b u v t ∈ S ↔ a t ∈ S ∧ t ∉ Ioo u v
  by_cases ht : t ∈ Ioo u v
  · rw [spliceFun_middle a b huv hs t ⟨ht.1.le,ht.2.le⟩]
    have hi := sliceParam_interior huv ht
    simp [ht,hS _ hi.1 hi.2]
  · rw [spliceFun_same_outside_open a b huv he ht]
    simp [ht]

lemma ordConnected_sdiff_Ioo {S : Set I} (hS : OrdConnected S) {u v : I}
    (huv : u < v) (hne : ¬(u ∈ S ∧ v ∈ S)) : OrdConnected (S \ Ioo u v) := by
  constructor
  intro x hx y hy t ht
  refine ⟨hS.out hx.1 hy.1 ht,?_⟩
  intro htm
  have hxu : x ≤ u := le_of_not_gt (fun h => hx.2 ⟨h,ht.1.trans_lt htm.2⟩)
  have hvy : v ≤ y := le_of_not_gt (fun h => hy.2 ⟨htm.1.trans_le ht.2,h⟩)
  exact hne ⟨hS.out hx.1 hy.1 ⟨hxu,huv.le.trans hvy⟩,
    hS.out hx.1 hy.1 ⟨hxu.trans huv.le,hvy⟩⟩

lemma splice_ordConnected (a b : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b)
    (S : Set X) (hS : ∀ t : I, 0<t → t<1 → b t ∉ S)
    (hc : OrdConnected (a ⁻¹' S)) (hne : ¬(b 0 ∈ S ∧ b 1 ∈ S)) :
    OrdConnected ((splice a b huv hs he ha) ⁻¹' S) := by
  rw [splice_preimage a b huv hs he ha S hS]
  apply ordConnected_sdiff_Ioo hc huv
  simpa only [mem_preimage,←hs,←he] using hne

lemma first_last [T2Space X] (a e : Arc X) (hne : (a ⁻¹' range e).Nonempty) :
    ∃ u v : I, u≤v ∧ a u ∈ range e ∧ a v ∈ range e ∧
      ∀ t : I, a t ∈ range e → t ∈ Icc u v := by
  have hc : IsCompact (a ⁻¹' range e) :=
    (e.compact_range.isClosed.preimage a.continuous).isCompact
  obtain ⟨u,hu⟩ := hc.exists_isLeast hne
  obtain ⟨v,hv⟩ := hc.exists_isGreatest hne
  exact ⟨u,v,hu.2 hv.1,hu.1,hv.1,fun t ht => ⟨hu.2 ht,hv.2 ht⟩⟩

lemma splice_target_preimage (a b e : Arc X) {u v : I} (huv : u < v)
    (hs : b 0 = a u) (he : b 1 = a v)
    (ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b)
    (hb : range b ⊆ range e)
    (hfirstlast : ∀ t : I, a t ∈ range e → t ∈ Icc u v) :
    (splice a b huv hs he ha) ⁻¹' range e = Icc u v := by
  ext t
  change spliceFun a b u v t ∈ range e ↔ t ∈ Icc u v
  by_cases ht : t ∈ Icc u v
  · rw [spliceFun_middle a b huv hs t ht]
    exact ⟨fun _ => ht,fun _ => hb (mem_range_self _)⟩
  · rw [spliceFun_outside a b ht]
    exact ⟨fun hm => (ht (hfirstlast t hm)).elim,fun hm => (ht hm).elim⟩

lemma subarc_interior_parameter {p q t : I} (hpq : p≠q) (ht₀ : 0<t) (ht₁ : t<1) :
    0 < Icc.convexComb p q t ∧ Icc.convexComb p q t < 1 := by
  have hpq' : (p : ℝ)≠q := fun h => hpq (Subtype.ext h)
  have ht₀' : (0:ℝ)<t := ht₀
  have ht₁' : (t:ℝ)<1 := ht₁
  rcases lt_or_gt_of_ne hpq' with h|h
  · have h₀ : (p:ℝ)<(1-(t:ℝ))*p+(t:ℝ)*q := by nlinarith
    have h₁ : (1-(t:ℝ))*p+(t:ℝ)*q<(q:ℝ) := by nlinarith
    exact ⟨lt_of_le_of_lt p.property.1 h₀,lt_of_lt_of_le h₁ q.property.2⟩
  · have h₀ : (q:ℝ)<(1-(t:ℝ))*p+(t:ℝ)*q := by nlinarith
    have h₁ : (1-(t:ℝ))*p+(t:ℝ)*q<(p:ℝ) := by nlinarith
    exact ⟨lt_of_le_of_lt q.property.1 h₀,lt_of_lt_of_le h₁ p.property.2⟩

def Compatible (e f : Arc X) : Prop :=
  (∀ s t : I, e s = f t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) ∧
  (range e ∩ range f).Subsingleton

lemma Compatible.symm {e f : Arc X} (h : Compatible e f) : Compatible f e := by
  constructor
  · intro s t he
    exact (h.1 t s he.symm).symm
  · simpa [inter_comm] using h.2

lemma Compatible.subarc_avoids {e f : Arc X} (h : Compatible e f)
    {p q : I} (hpq : p≠q) (t : I) (ht₀ : 0<t) (ht₁ : t<1) :
    e.subarc p q hpq t ∉ range f := by
  rintro ⟨s,hs⟩
  have hi := subarc_interior_parameter hpq ht₀ ht₁
  rcases (h.1 (Icc.convexComb p q t) s hs.symm).1 with he|he
  · exact (ne_of_gt hi.1) he
  · exact (ne_of_lt hi.2) he

lemma Compatible.subarc_not_both {e f : Arc X} (h : Compatible e f)
    {p q : I} (hpq : p≠q) : ¬(e.subarc p q hpq 0 ∈ range f ∧
      e.subarc p q hpq 1 ∈ range f) := by
  simp only [subarc_zero,subarc_one]
  rintro ⟨hp,hq⟩
  exact hpq (e.injective (h.2 ⟨mem_range_self _,hp⟩ ⟨mem_range_self _,hq⟩))

theorem repair_one [T2Space X] (a e : Arc X) :
    ∃ a' : Arc X, a' 0 = a 0 ∧ a' 1 = a 1 ∧
      OrdConnected (a' ⁻¹' range e) ∧
      range a' ⊆ range a ∪ range e ∧
      (∀ f : Arc X, Compatible e f →
        range a' ∩ range f ⊆ range a ∩ range f) ∧
      (∀ f : Arc X, Compatible e f → OrdConnected (a ⁻¹' range f) →
        OrdConnected (a' ⁻¹' range f)) ∧
      ((range a ∩ range e).Nonempty ∨ a'=a) := by
  classical
  by_cases hne : (a ⁻¹' range e).Nonempty
  · obtain ⟨u,v,huv,hu,hv,hfl⟩ := first_last a e hne
    have hmeet : (range a ∩ range e).Nonempty := ⟨a u,mem_range_self _,hu⟩
    rcases eq_or_lt_of_le huv with heq|huv
    · have hsingle : a ⁻¹' range e = {u} := by
        ext t
        constructor
        · intro ht
          apply mem_singleton_iff.mpr
          have h := hfl t ht
          exact le_antisymm (heq ▸ h.2) h.1
        · intro ht
          have htu : t=u := mem_singleton_iff.mp ht
          subst t
          exact hu
      refine ⟨a,rfl,rfl,?_,subset_union_left,fun _ _ => subset_rfl,
        fun _ _ h => h,Or.inl hmeet⟩
      rw [hsingle]
      exact ordConnected_singleton
    · obtain ⟨p,hp⟩ := hu
      obtain ⟨q,hq⟩ := hv
      have hpq : p≠q := by
        intro h
        have hav : a u = a v := hp.symm.trans ((congrArg e h).trans hq)
        exact huv.ne (a.injective hav)
      let b := e.subarc p q hpq
      have hs : b 0 = a u := (subarc_zero e p q hpq).trans hp
      have he : b 1 = a v := (subarc_one e p q hpq).trans hq
      have hb : range b ⊆ range e := subarc_range_subset e p q hpq
      have ha : ∀ t : I, t ∉ Icc u v → a t ∉ range b :=
        fun t ht hm => ht (hfl t (hb hm))
      let a' := splice a b huv hs he ha
      refine ⟨a',splice_zero a b huv hs he ha,splice_one a b huv hs he ha,?_,?_,?_,?_,
        Or.inl hmeet⟩
      · rw [splice_target_preimage a b e huv hs he ha hb hfl]
        exact ordConnected_Icc
      · exact (splice_range_subset a b huv hs he ha).trans (union_subset_union subset_rfl hb)
      · intro f hf x hx
        obtain ⟨t,ht⟩ := hx.1
        have ht' : t ∈ a' ⁻¹' range f := by
          change a' t ∈ range f
          rw [ht]
          exact hx.2
        rw [splice_preimage a b huv hs he ha (range f)
          (fun t ht₀ ht₁ => hf.subarc_avoids hpq t ht₀ ht₁)] at ht'
        have heval : a' t = a t := spliceFun_same_outside_open a b huv he ht'.2
        exact ⟨⟨t,heval.symm.trans ht⟩,hx.2⟩
      · intro f hf hc
        exact splice_ordConnected a b huv hs he ha (range f)
          (fun t ht₀ ht₁ => hf.subarc_avoids hpq t ht₀ ht₁) hc
          (hf.subarc_not_both hpq)
  · have hempty : a ⁻¹' range e = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨a,rfl,rfl,?_,subset_union_left,fun _ _ => subset_rfl,
      fun _ _ h => h,Or.inr rfl⟩
    rw [hempty]
    exact ordConnected_empty

theorem repair_finite [T2Space X] {ι : Type*} (E : ι → Arc X) (S : Finset ι)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i≠j → Compatible (E i) (E j)) (a : Arc X) :
    ∃ a' : Arc X, a' 0 = a 0 ∧ a' 1 = a 1 ∧
      (∀ i ∈ S, OrdConnected (a' ⁻¹' range (E i))) ∧
      (∀ x ∈ range a', x ∈ range a ∨ ∃ i ∈ S,
        x ∈ range (E i) ∧ (range a ∩ range (E i)).Nonempty) ∧
      (∀ f : Arc X, (∀ i ∈ S, Compatible (E i) f) →
        range a' ∩ range f ⊆ range a ∩ range f) ∧
      (∀ f : Arc X, (∀ i ∈ S, Compatible (E i) f) →
        OrdConnected (a ⁻¹' range f) → OrdConnected (a' ⁻¹' range f)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨a,rfl,rfl,by simp,fun _ hx => Or.inl hx,fun _ _ => subset_rfl,
      fun _ _ h => h⟩
  | @insert i S hi ih =>
    have hpairS : ∀ i ∈ S, ∀ j ∈ S, i≠j → Compatible (E i) (E j) :=
      fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk
    obtain ⟨a₁,h₀,h₁,hconn,hsupp,hold,hretain⟩ := ih hpairS
    have hcomp : ∀ j ∈ S, Compatible (E j) (E i) := by
      intro j hj
      exact hpair j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
        (fun h => hi (h ▸ hj))
    have hcross := hold (E i) hcomp
    obtain ⟨a₂,h₂₀,h₂₁,h₂conn,h₂supp,h₂old,h₂retain,h₂change⟩ := repair_one a₁ (E i)
    refine ⟨a₂,h₂₀.trans h₀,h₂₁.trans h₁,?_,?_,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact h₂conn
      · exact h₂retain (E j) (hcomp j hj).symm (hconn j hj)
    · intro x hx
      by_cases hx₁ : x ∈ range a₁
      · rcases hsupp x hx₁ with hx₀|⟨j,hj,hxj,hjmeet⟩
        · exact Or.inl hx₀
        · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,hxj,hjmeet⟩
      · have hxi : x ∈ range (E i) := (h₂supp hx).resolve_left hx₁
        have hmeet : (range a ∩ range (E i)).Nonempty := by
          rcases h₂change with ⟨y,hy⟩|heq
          · exact ⟨y,hcross hy⟩
          · exact False.elim (hx₁ (heq ▸ hx))
        exact Or.inr ⟨i,Finset.mem_insert_self _ _,hxi,hmeet⟩
    · intro f hf
      exact (h₂old f (hf i (Finset.mem_insert_self _ _))).trans
        (hold f (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    · intro f hf hc
      exact h₂retain f (hf i (Finset.mem_insert_self _ _))
        (hretain f (fun j hj => hf j (Finset.mem_insert_of_mem hj)) hc)

lemma intersection_preconnected (a e : Arc X) (hc : OrdConnected (a ⁻¹' range e)) :
    IsPreconnected (range a ∩ range e) := by
  have h := hc.isPreconnected.image a a.continuous.continuousOn
  rwa [image_preimage_eq_inter_range,inter_comm] at h

section Metric
variable {Y : Type*} [MetricSpace Y]

theorem repair_finite_bounded {ι : Type*} (E : ι → Arc Y) (S : Finset ι)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i≠j → Compatible (E i) (E j))
    (a : Arc Y) {B : ℝ} (hB : 0≤B) (hb : ∀ i ∈ S, Metric.diam (range (E i)) ≤ B) :
    ∃ a' : Arc Y, a' 0 = a 0 ∧ a' 1 = a 1 ∧
      (∀ i ∈ S, OrdConnected (a' ⁻¹' range (E i))) ∧
      (∀ x ∈ range a', ∃ y ∈ range a, dist x y ≤ B) ∧
      Metric.diam (range a') ≤ Metric.diam (range a)+2*B := by
  obtain ⟨a',h₀,h₁,hconn,hsupp,_⟩ := repair_finite E S hpair a
  have hnear : ∀ x ∈ range a', ∃ y ∈ range a, dist x y ≤ B := by
    intro x hx
    rcases hsupp x hx with hxa|⟨i,hi,hxe,y,hya,hye⟩
    · exact ⟨x,hxa,by simpa using hB⟩
    · exact ⟨y,hya,(Metric.dist_le_diam_of_mem (E i).compact_range.isBounded hxe hye).trans
        (hb i hi)⟩
  refine ⟨a',h₀,h₁,hconn,hnear,?_⟩
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨x₀,hx₀,hxx₀⟩ := hnear x hx
  obtain ⟨y₀,hy₀,hyy₀⟩ := hnear y hy
  have hxy₀ := Metric.dist_le_diam_of_mem a.compact_range.isBounded hx₀ hy₀
  have htri := dist_triangle4 x x₀ y₀ y
  rw [dist_comm y₀ y] at htri
  linarith

lemma separated_of_near (a b a' b' : Arc Y) {B L : ℝ}
    (ha : ∀ x ∈ range a', ∃ y ∈ range a, dist x y ≤ B)
    (hb : ∀ x ∈ range b', ∃ y ∈ range b, dist x y ≤ B)
    (hsep : ∀ x ∈ range a, ∀ y ∈ range b, L+2*B < dist x y) :
    ∀ x ∈ range a', ∀ y ∈ range b', L < dist x y := by
  intro x hx y hy
  obtain ⟨x₀,hx₀,hxx₀⟩ := ha x hx
  obtain ⟨y₀,hy₀,hyy₀⟩ := hb y hy
  have hfar := hsep x₀ hx₀ y₀ hy₀
  have htri := dist_triangle4 x₀ x y y₀
  rw [dist_comm x₀ x] at htri
  linarith

lemma meets_at_most_one (a b e : Arc Y) {B : ℝ}
    (hsep : ∀ x ∈ range a, ∀ y ∈ range b, B < dist x y)
    (he : Metric.diam (range e) ≤ B) :
    ¬ ((range a ∩ range e).Nonempty ∧ (range b ∩ range e).Nonempty) := by
  rintro ⟨⟨x,hxa,hxe⟩,⟨y,hyb,hye⟩⟩
  exact (hsep x hxa y hyb).not_ge
    ((Metric.dist_le_diam_of_mem e.compact_range.isBounded hxe hye).trans he)

end Metric

section Convex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

def mappedSegment (e : E → X) (he : Continuous e) (hinj : Function.Injective e)
    (x y : E) (hxy : x≠y) : Arc X where
  map := ⟨fun t => e (Path.segment x y t),he.comp (Path.segment x y).continuous⟩
  injective := hinj.comp (Path.segment_injective_of_ne hxy)

@[simp] lemma mappedSegment_zero (e : E → X) (he : Continuous e)
    (hinj : Function.Injective e) (x y : E) (hxy : x≠y) :
    mappedSegment e he hinj x y hxy 0 = e x := by simp [mappedSegment]
@[simp] lemma mappedSegment_one (e : E → X) (he : Continuous e)
    (hinj : Function.Injective e) (x y : E) (hxy : x≠y) :
    mappedSegment e he hinj x y hxy 1 = e y := by simp [mappedSegment]

lemma mappedSegment_range (e : E → X) (he : Continuous e)
    (hinj : Function.Injective e) (x y : E) (hxy : x≠y)
    {C : Set E} (hC : Convex ℝ C) (hx : x∈C) (hy : y∈C) :
    range (mappedSegment e he hinj x y hxy) ⊆ e '' C := by
  rintro _ ⟨t,rfl⟩
  refine ⟨Path.segment x y t,?_,rfl⟩
  rw [Path.segment_apply]
  exact hC.segment_subset hx hy (lineMap_mem_segment ℝ x y t.property)

end Convex

end Arc
end CannonEmbeddedArc

end
end
end
end

end OAI
