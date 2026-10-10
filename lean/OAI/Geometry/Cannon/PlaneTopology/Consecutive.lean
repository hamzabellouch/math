import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Arc

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma interval_of_ordConnected [T2Space X] (a e : Arc X)
    (hc : OrdConnected (a ⁻¹' range e)) :
    (a ⁻¹' range e)=∅ ∨ ∃ u v : I, u≤v ∧ a ⁻¹' range e=Icc u v := by
  by_cases hne : (a ⁻¹' range e).Nonempty
  · obtain ⟨u,v,huv,hu,hv,hfl⟩ := first_last a e hne
    exact Or.inr ⟨u,v,huv,Subset.antisymm hfl (hc.out hu hv)⟩
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

lemma intersection_ordConnected_symm [T2Space X] (a e : Arc X)
    (hc : OrdConnected (a ⁻¹' range e)) : OrdConnected (e ⁻¹' range a) := by
  apply IsPreconnected.ordConnected
  apply (e.continuous.isClosedEmbedding e.injective).isEmbedding.isInducing.isPreconnected_image.mp
  rw [image_preimage_eq_inter_range]
  exact intersection_preconnected a e hc

theorem finite_breakpoints [T2Space X] {ι : Type*} (E : ι → Arc X)
    (S : Finset ι) (a : Arc X) (hc : ∀ i ∈ S, OrdConnected (a ⁻¹' range (E i))) :
    ∃ P : Finset I, 0∈P ∧ 1∈P ∧ P.card ≤ 2*S.card+2 ∧
      ∀ i ∈ S, (a ⁻¹' range (E i))=∅ ∨
        ∃ u∈P, ∃ v∈P, u≤v ∧ a ⁻¹' range (E i)=Icc u v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨{0,1},by simp,by simp,by simp,?_⟩
    simp
  | @insert i S hi ih =>
    obtain ⟨P,hP₀,hP₁,hcard,hP⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    rcases interval_of_ordConnected a (E i) (hc i (Finset.mem_insert_self _ _)) with he|⟨u,v,huv,he⟩
    · refine ⟨P,hP₀,hP₁,hcard.trans ?_,?_⟩
      · simp only [Finset.card_insert_of_notMem hi]
        omega
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact Or.inl he
        · exact hP j hj
    · let Q := insert u (insert v P)
      have hPQ : P ⊆ Q := Finset.subset_insert _ _ |>.trans (Finset.subset_insert _ _)
      refine ⟨Q,hPQ hP₀,hPQ hP₁,?_,?_⟩
      · have hv := Finset.card_insert_le v P
        have hu := Finset.card_insert_le u (insert v P)
        simp only [Finset.card_insert_of_notMem hi]
        change (insert u (insert v P)).card ≤ _
        omega
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact Or.inr ⟨u,Finset.mem_insert_self _ _,v,
            Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),huv,he⟩
        · rcases hP j hj with he|⟨p,hp,q,hq,hpq,he⟩
          · exact Or.inl he
          · exact Or.inr ⟨p,hPQ hp,q,hPQ hq,hpq,he⟩

def Consecutive (P : Finset I) (p q : I) : Prop :=
  p∈P ∧ q∈P ∧ p<q ∧ ∀ t∈P, p<t → t<q → False

lemma consecutive_cover (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P) (t : I) :
    ∃ p q : I, Consecutive P p q ∧ t ∈ Icc p q := by
  classical
  by_cases ht : t<1
  · let L := P.filter (· ≤ t)
    let R := P.filter (t < ·)
    have hL : L.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨h₀,unitInterval.nonneg t⟩⟩
    have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,ht⟩⟩
    let p := L.max' hL
    let q := R.min' hR
    have hp := Finset.mem_filter.mp (Finset.max'_mem L hL)
    have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
    refine ⟨p,q,⟨hp.1,hq.1,hp.2.trans_lt hq.2,?_⟩,hp.2,hq.2.le⟩
    intro z hz hpz hzq
    rcases le_or_gt z t with hzt|htz
    · exact hpz.not_ge (Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz,hzt⟩))
    · exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,htz⟩))
  · have ht₁ : t=1 := le_antisymm (unitInterval.le_one t) (le_of_not_gt ht)
    subst t
    let L := P.filter (· < 1)
    have hL : L.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨h₀,zero_lt_one⟩⟩
    let p := L.max' hL
    have hp := Finset.mem_filter.mp (Finset.max'_mem L hL)
    refine ⟨p,1,⟨hp.1,h₁,hp.2,?_⟩,hp.2.le,le_rfl⟩
    intro z hz hpz hz₁
    exact hpz.not_ge (Finset.le_max' L z (Finset.mem_filter.mpr ⟨hz,hz₁⟩))

lemma convexComb_sliceParam {u v : I} (huv : u<v) (t : I) (ht : t∈Icc u v) :
    Icc.convexComb u v (sliceParam huv t ht)=t := by
  exact (Icc.eq_convexComb ht.1 ht.2).symm

lemma subarc_range_eq (a : Arc X) {p q : I} (hpq : p<q) :
    range (a.subarc p q hpq.ne) = a '' Icc p q := by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    exact ⟨Icc.convexComb p q t,⟨Icc.le_convexComb hpq.le t,Icc.convexComb_le hpq.le t⟩,rfl⟩
  · rintro _ ⟨t,ht,rfl⟩
    refine ⟨sliceParam hpq t ht,?_⟩
    change a (Icc.convexComb p q (sliceParam hpq t ht))=a t
    rw [convexComb_sliceParam]

lemma Consecutive.ordered {P : Finset I} {p q r s : I}
    (hpq : Consecutive P p q) (hrs : Consecutive P r s)
    (hne : (p,q) ≠ (r,s)) : q≤r ∨ s≤p := by
  rcases lt_trichotomy p r with hpr|hpr|hrp
  · exact Or.inl (le_of_not_gt (fun hrq => hpq.2.2.2 r hrs.1 hpr hrq))
  · subst r
    rcases lt_trichotomy q s with hqs|hqs|hsq
    · exact False.elim (hrs.2.2.2 q hpq.2.1 hpq.2.2.1 hqs)
    · exact False.elim (hne (by simp [hqs]))
    · exact False.elim (hpq.2.2.2 s hrs.2.1 hrs.2.2.1 hsq)
  · exact Or.inr (le_of_not_gt (fun hps => hrs.2.2.2 p hpq.1 hrp hps))

lemma ordered_subarcs_meeting (a : Arc X) {p q r s : I} (hpq : p<q) (hrs : r<s)
    (hqr : q≤r) (t w : I)
    (he : a.subarc p q hpq.ne t=a.subarc r s hrs.ne w) : t=1 ∧ w=0 := by
  have hc : Icc.convexComb p q t=Icc.convexComb r s w := a.injective he
  have htq : Icc.convexComb p q t=q := le_antisymm (Icc.convexComb_le hpq.le t)
    (hqr.trans ((Icc.le_convexComb hrs.le w).trans_eq hc.symm))
  have hwr : Icc.convexComb r s w=r := le_antisymm
    (hc.symm.trans_le ((Icc.convexComb_le hpq.le t).trans hqr)) (Icc.le_convexComb hrs.le w)
  constructor
  · apply (a.subarc p q hpq.ne).injective
    change a (Icc.convexComb p q t)=a (Icc.convexComb p q 1)
    rw [htq,Icc.convexComb_one]
  · apply (a.subarc r s hrs.ne).injective
    change a (Icc.convexComb r s w)=a (Icc.convexComb r s 0)
    rw [hwr,Icc.convexComb_zero]

lemma ordered_subarcs_compatible (a : Arc X) {p q r s : I}
    (hpq : p<q) (hrs : r<s) (hqr : q≤r) :
    Compatible (a.subarc p q hpq.ne) (a.subarc r s hrs.ne) := by
  constructor
  · intro t w he
    obtain ⟨ht,hw⟩ := ordered_subarcs_meeting a hpq hrs hqr t w he
    exact ⟨Or.inr ht,Or.inl hw⟩
  · intro x hx y hy
    obtain ⟨t,ht⟩ := hx.1
    obtain ⟨w,hw⟩ := hx.2
    obtain ⟨u,hu⟩ := hy.1
    obtain ⟨v,hv⟩ := hy.2
    have ht₁ := (ordered_subarcs_meeting a hpq hrs hqr t w (ht.trans hw.symm)).1
    have hu₁ := (ordered_subarcs_meeting a hpq hrs hqr u v (hu.trans hv.symm)).1
    exact ht.symm.trans ((congrArg (a.subarc p q hpq.ne) (ht₁.trans hu₁.symm)).trans hu)

def segments (P : Finset I) : Finset (I×I) := by
  classical
  exact (P.product P).filter (fun z => Consecutive P z.1 z.2)

lemma mem_segments (P : Finset I) (p q : I) :
    (p,q)∈segments P ↔ Consecutive P p q := by
  classical
  unfold segments
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨Finset.mem_product.mpr ⟨h.1,h.2.1⟩,h⟩⟩

lemma segments_card (P : Finset I) : (segments P).card ≤ P.card^2 := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp [Finset.card_product,pow_two])

lemma segment_consecutive (P : Finset I) (z : segments P) :
    Consecutive P z.val.1 z.val.2 := (mem_segments P _ _).mp z.property

def subdivArc (a : Arc X) (P : Finset I) (z : segments P) : Arc X :=
  a.subarc z.val.1 z.val.2 (segment_consecutive P z).2.2.1.ne

@[simp] lemma subdivArc_zero (a : Arc X) (P : Finset I) (z : segments P) :
    subdivArc a P z 0=a z.val.1 := subarc_zero _ _ _ _
@[simp] lemma subdivArc_one (a : Arc X) (P : Finset I) (z : segments P) :
    subdivArc a P z 1=a z.val.2 := subarc_one _ _ _ _

lemma subdivArc_range_eq (a : Arc X) (P : Finset I) (z : segments P) :
    range (subdivArc a P z)=a '' Icc z.val.1 z.val.2 :=
  subarc_range_eq a (segment_consecutive P z).2.2.1

lemma subdivision_cover (a : Arc X) (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P) :
    range a=⋃ z : segments P, range (subdivArc a P z) := by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    obtain ⟨p,q,hpq,ht⟩ := consecutive_cover P h₀ h₁ t
    let z : segments P := ⟨(p,q),(mem_segments P p q).mpr hpq⟩
    apply mem_iUnion.mpr
    refine ⟨z,?_⟩
    rw [subdivArc_range_eq]
    exact ⟨t,ht,rfl⟩
  · intro x hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hx
    exact subarc_range_subset a _ _ _ hz

lemma subdivision_compatible (a : Arc X) (P : Finset I) :
    ∀ z w : segments P, z≠w → Compatible (subdivArc a P z) (subdivArc a P w) := by
  intro z w hzw
  have hz := segment_consecutive P z
  have hw := segment_consecutive P w
  have hne : z.val ≠ w.val := fun h => hzw (Subtype.ext h)
  rcases hz.ordered hw hne with h|h
  · exact ordered_subarcs_compatible a hz.2.2.1 hw.2.2.1 h
  · exact (ordered_subarcs_compatible a hw.2.2.1 hz.2.2.1 h).symm

lemma convexComb_injective {p q : I} (hpq : p<q) : Function.Injective (Icc.convexComb p q) := by
  intro s t h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  simp only [Icc.coe_convexComb] at hh
  have : ((s : ℝ)-t)*((q : ℝ)-p)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (ne_of_gt (sub_pos.mpr hpq)))

lemma Consecutive.marked_parameter {P : Finset I} {p q : I}
    (hpq : Consecutive P p q) (t : I) (ht : Icc.convexComb p q t∈P) : t=0 ∨ t=1 := by
  have hlo := Icc.le_convexComb hpq.2.2.1.le t
  have hhi := Icc.convexComb_le hpq.2.2.1.le t
  by_cases hl : Icc.convexComb p q t=p
  · exact Or.inl (convexComb_injective hpq.2.2.1 (hl.trans (Icc.convexComb_zero p q).symm))
  · have hr : Icc.convexComb p q t=q := by
      by_contra hr
      exact hpq.2.2.2 _ ht (lt_of_le_of_ne hlo (Ne.symm hl)) (lt_of_le_of_ne hhi hr)
    exact Or.inr (convexComb_injective hpq.2.2.1 (hr.trans (Icc.convexComb_one p q).symm))

lemma subarc_parameter_endpoint {p q t : I} (hpq : p<q)
    (ht : Icc.convexComb p q t=0 ∨ Icc.convexComb p q t=1) : t=0 ∨ t=1 := by
  have hlo := Icc.le_convexComb hpq.le t
  have hhi := Icc.convexComb_le hpq.le t
  rcases ht with ht|ht
  · have hp : p=0 := le_antisymm (ht ▸ hlo) (unitInterval.nonneg p)
    exact Or.inl (convexComb_injective hpq (ht.trans (hp.symm.trans (Icc.convexComb_zero p q).symm)))
  · have hq : q=1 := le_antisymm (unitInterval.le_one q) (ht ▸ hhi)
    exact Or.inr (convexComb_injective hpq (ht.trans (hq.symm.trans (Icc.convexComb_one p q).symm)))

lemma Compatible.subarcs {a b : Arc X} (hab : Compatible a b)
    {p q r s : I} (hpq : p<q) (hrs : r<s) :
    Compatible (a.subarc p q hpq.ne) (b.subarc r s hrs.ne) := by
  constructor
  · intro t w he
    obtain ⟨ht,hw⟩ := hab.1 (Icc.convexComb p q t) (Icc.convexComb r s w) he
    exact ⟨subarc_parameter_endpoint hpq ht,subarc_parameter_endpoint hrs hw⟩
  · exact hab.2.anti (inter_subset_inter (subarc_range_subset a p q hpq.ne)
      (subarc_range_subset b r s hrs.ne))

lemma Consecutive.interval_dichotomy {P : Finset I} {p q u v : I}
    (hpq : Consecutive P p q) (hu : u∈P) (hv : v∈P) :
    Icc p q ⊆ Icc u v ∨ ∀ t∈Icc p q ∩ Icc u v, t=p ∨ t=q := by
  by_cases hs : Icc p q ⊆ Icc u v
  · exact Or.inl hs
  · refine Or.inr (fun t ht => ?_)
    by_cases htp : t=p
    · exact Or.inl htp
    by_cases htq : t=q
    · exact Or.inr htq
    have hpt : p<t := lt_of_le_of_ne ht.1.1 (Ne.symm htp)
    have htq : t<q := lt_of_le_of_ne ht.1.2 htq
    have hup : u≤p := le_of_not_gt (fun hpu => hpq.2.2.2 u hu hpu (ht.2.1.trans_lt htq))
    have hqv : q≤v := le_of_not_gt (fun hvq => hpq.2.2.2 v hv (hpt.trans_le ht.2.2) hvq)
    exact False.elim (hs (Icc_subset_Icc hup hqv))

lemma free_segment_intersection {a e : Arc X} {P : Finset I} {p q : I}
    (hpq : Consecutive P p q)
    (he : (a ⁻¹' range e)=∅ ∨ ∃ u∈P, ∃ v∈P, u≤v ∧ a ⁻¹' range e=Icc u v)
    (hfree : ¬ range (a.subarc p q hpq.2.2.1.ne) ⊆ range e) :
    (∀ t : I, a.subarc p q hpq.2.2.1.ne t∈range e → t=0 ∨ t=1) ∧
    (range (a.subarc p q hpq.2.2.1.ne) ∩ range e).Subsingleton := by
  rcases he with he|⟨u,hu,v,hv,huv,he⟩
  · have hn (t : I) (ht : a.subarc p q hpq.2.2.1.ne t∈range e) : False := by
      have : Icc.convexComb p q t∈a ⁻¹' range e := ht
      rw [he] at this
      exact this
    exact ⟨fun t ht => (hn t ht).elim,fun x ⟨⟨t,ht⟩,hx⟩ y _ => (hn t (ht ▸ hx)).elim⟩
  · have hns : ¬ Icc p q ⊆ Icc u v := by
      intro hs
      apply hfree
      rw [subarc_range_eq a hpq.2.2.1]
      rintro x ⟨t,ht,rfl⟩
      change t∈a ⁻¹' range e
      rw [he]
      exact hs ht
    have hends := (hpq.interval_dichotomy hu hv).resolve_left hns
    have hend (t : I) (ht : a.subarc p q hpq.2.2.1.ne t∈range e) : t=0 ∨ t=1 := by
      have ht' : Icc.convexComb p q t∈Icc u v := he ▸ ht
      rcases hends _ ⟨⟨Icc.le_convexComb hpq.2.2.1.le t,Icc.convexComb_le hpq.2.2.1.le t⟩,ht'⟩ with hl|hr
      · exact Or.inl (convexComb_injective hpq.2.2.1 (hl.trans (Icc.convexComb_zero p q).symm))
      · exact Or.inr (convexComb_injective hpq.2.2.1 (hr.trans (Icc.convexComb_one p q).symm))
    refine ⟨hend,?_⟩
    have hnotboth : ¬ (a p∈range e ∧ a q∈range e) := by
      rintro ⟨hp,hq⟩
      apply hns
      have hp' : p∈Icc u v := he ▸ hp
      have hq' : q∈Icc u v := he ▸ hq
      exact Icc_subset_Icc hp'.1 hq'.2
    rintro x ⟨⟨t,rfl⟩,ht⟩ y ⟨⟨w,rfl⟩,hw⟩
    rcases hend t ht with rfl|rfl <;> rcases hend w hw with rfl|rfl
    · rfl
    · exact (hnotboth (by simpa using And.intro ht hw)).elim
    · exact (hnotboth (by simpa using And.intro hw ht)).elim
    · rfl

theorem old_breakpoints (a e : Arc X) (P : Finset I) :
    ∃ Q : Finset I, 0∈Q ∧ 1∈Q ∧ Q.card ≤ P.card+2 ∧
      ∀ t : I, e t∈a '' (P : Set I) → t∈Q := by
  classical
  let T : Set I := e ⁻¹' (a '' (P : Set I))
  have hTf : T.Finite := ((Finset.finite_toSet P).image a).preimage e.injective.injOn
  let Q := insert 0 (insert 1 hTf.toFinset)
  have hcard : hTf.toFinset.card ≤ P.card := by
    calc
      _ = T.ncard := (Set.ncard_eq_toFinset_card T hTf).symm
      _ ≤ (a '' (P : Set I)).ncard := Set.ncard_le_ncard_of_injOn e (fun _ ht => ht) e.injective.injOn ((Finset.finite_toSet P).image a)
      _ ≤ (P : Set I).ncard := Set.ncard_image_le
      _ = P.card := Set.ncard_coe_finset P
  refine ⟨Q,Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),?_,?_⟩
  · have h₁ := Finset.card_insert_le 1 hTf.toFinset
    have h₀ := Finset.card_insert_le 0 (insert 1 hTf.toFinset)
    dsimp [Q]
    omega
  · intro t ht
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hTf.mem_toFinset.mpr ht))

lemma free_segment_compatible_old_subdivision {a e : Arc X} {P Q : Finset I}
    {p q r s : I} (hpq : Consecutive P p q) (hrs : Consecutive Q r s)
    (he : (a ⁻¹' range e)=∅ ∨ ∃ u∈P, ∃ v∈P, u≤v ∧ a ⁻¹' range e=Icc u v)
    (hfree : ¬ range (a.subarc p q hpq.2.2.1.ne) ⊆ range e)
    (hmark : ∀ t : I, e t∈a '' (P : Set I) → t∈Q) :
    Compatible (a.subarc p q hpq.2.2.1.ne) (e.subarc r s hrs.2.2.1.ne) := by
  obtain ⟨hend,hsub⟩ := free_segment_intersection hpq he hfree
  constructor
  · intro t w heq
    have ht := hend t ⟨Icc.convexComb r s w,heq.symm⟩
    refine ⟨ht,hrs.marked_parameter w (hmark _ ?_)⟩
    rcases ht with rfl|rfl
    · exact ⟨p,hpq.1,(subarc_zero a _ _ _).symm.trans heq⟩
    · exact ⟨q,hpq.2.1,(subarc_one a _ _ _).symm.trans heq⟩
  · exact hsub.anti (inter_subset_inter_right _ (subarc_range_subset e r s _))

end Arc
end CannonEmbeddedArc

noncomputable section
namespace CannonEmbeddedArc
open Set unitInterval

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma subdivArc_range_subset (a : Arc X) (P : Finset I) (z : segments P) :
    range (subdivArc a P z) ⊆ range a :=
  subarc_range_subset a _ _ (segment_consecutive P z).2.2.1.ne

lemma Compatible.of_disjoint {a b : Arc X} (h : Disjoint (range a) (range b)) :
    Compatible a b := by
  constructor
  · intro t w heq
    exact (Set.disjoint_left.mp h (mem_range_self t) ⟨w,heq.symm⟩).elim
  · intro x hx y _
    exact (Set.disjoint_left.mp h hx.1 hx.2).elim

def Vertex {ι : Type*} (E : ι → Arc X) (x : X) : Prop :=
  ∃ i, E i 0=x ∨ E i 1=x

lemma subdivision_mark_vertex (a : Arc X) (P : Finset I) (h₀ : 0∈P) (h₁ : 1∈P)
    {t : I} (ht : t∈P) : Vertex (subdivArc a P) (a t) := by
  obtain ⟨p,q,hpq,hpt,htq⟩ := consecutive_cover P h₀ h₁ t
  let z : segments P := ⟨(p,q),(mem_segments P p q).mpr hpq⟩
  refine ⟨z,?_⟩
  by_cases htp : t=p
  · exact Or.inl (by simp [z,htp])
  · have htq : t=q := by
      by_contra h
      exact hpq.2.2.2 t ht (lt_of_le_of_ne hpt (Ne.symm htp)) (lt_of_le_of_ne htq h)
    exact Or.inr (by simp [z,htq])

variable {ι κ : Type*} (E : ι → Arc X) (A : κ → Arc X)
    (P : κ → Finset I) (Q : ι → Finset I)

def FreeSegment (i : κ) (z : segments (P i)) : Prop :=
  ∀ e, ¬range (subdivArc (A i) (P i) z) ⊆ range (E e)

def RefinementIndex := (Σ e : ι, segments (Q e)) ⊕
  (Σ i : κ, {z : segments (P i) // FreeSegment E A P i z})

instance [Fintype ι] [Fintype κ] : Fintype (RefinementIndex E A P Q) := by
  classical
  unfold RefinementIndex
  infer_instance

def refinementArc : RefinementIndex E A P Q → Arc X
  | Sum.inl ⟨e,z⟩ => subdivArc (E e) (Q e) z
  | Sum.inr ⟨i,z⟩ => subdivArc (A i) (P i) z.val

variable (hE : Pairwise (fun e f => Compatible (E e) (E f)))
    (hA : Pairwise (fun i j => Disjoint (range (A i)) (range (A j))))
    (hinterval : ∀ i e, (A i ⁻¹' range (E e))=∅ ∨
      ∃ u∈P i, ∃ v∈P i, u≤v ∧ A i ⁻¹' range (E e)=Icc u v)
    (hmark : ∀ i e t, E e t∈A i '' (P i : Set I) → t∈Q e)

include hE hA hinterval hmark in
lemma refinement_compatible : Pairwise (fun z w : RefinementIndex E A P Q =>
    Compatible (refinementArc E A P Q z) (refinementArc E A P Q w)) := by
  intro z w hzw
  rcases z with ⟨e,z⟩|⟨i,z⟩ <;> rcases w with ⟨f,w⟩|⟨j,w⟩
  · by_cases hef : e=f
    · subst f
      have hne : z≠w := fun h => hzw (by cases h; rfl)
      exact subdivision_compatible (E e) (Q e) z w hne
    · exact (hE hef).subarcs (segment_consecutive (Q e) z).2.2.1
        (segment_consecutive (Q f) w).2.2.1
  · exact (free_segment_compatible_old_subdivision
      (segment_consecutive (P j) w.val) (segment_consecutive (Q e) z)
      (hinterval j e) (w.property e) (hmark j e)).symm
  · exact free_segment_compatible_old_subdivision
      (segment_consecutive (P i) z.val) (segment_consecutive (Q f) w)
      (hinterval i f) (z.property f) (hmark i f)
  · by_cases hij : i=j
    · subst j
      have hne : z.val≠w.val := fun h => hzw (by have heq : z=w := Subtype.ext h; cases heq; rfl)
      exact subdivision_compatible (A i) (P i) z.val w.val hne
    · apply Compatible.of_disjoint
      exact (hA hij).mono (subdivArc_range_subset (A i) (P i) z.val) (subdivArc_range_subset (A j) (P j) w.val)

variable (hP₀ : ∀ i, 0∈P i) (hP₁ : ∀ i, 1∈P i)
    (hQ₀ : ∀ e, 0∈Q e) (hQ₁ : ∀ e, 1∈Q e)

include hQ₀ hQ₁ in
lemma refinement_old_subset (e : ι) : range (E e) ⊆ ⋃ z, range (refinementArc E A P Q z) := by
  rw [subdivision_cover (E e) (Q e) (hQ₀ e) (hQ₁ e)]
  intro x hx
  obtain ⟨z,hz⟩ := mem_iUnion.mp hx
  exact mem_iUnion_of_mem (Sum.inl ⟨e,z⟩) hz

include hP₀ hP₁ hQ₀ hQ₁ in
lemma refinement_cover : (⋃ e, range (E e)) ∪ (⋃ i, range (A i)) =
    ⋃ z, range (refinementArc E A P Q z) := by
  classical
  apply Subset.antisymm
  · intro x hx
    rcases hx with hx|hx
    · obtain ⟨e,he⟩ := mem_iUnion.mp hx
      exact refinement_old_subset E A P Q hQ₀ hQ₁ e he
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      rw [subdivision_cover (A i) (P i) (hP₀ i) (hP₁ i)] at hi
      obtain ⟨z,hz⟩ := mem_iUnion.mp hi
      by_cases hf : FreeSegment E A P i z
      · exact mem_iUnion_of_mem (Sum.inr ⟨i,⟨z,hf⟩⟩) hz
      · obtain ⟨e,he⟩ : ∃ e, range (subdivArc (A i) (P i) z) ⊆ range (E e) := by
          simpa only [FreeSegment,not_forall,not_not] using hf
        exact refinement_old_subset E A P Q hQ₀ hQ₁ e (he hz)
  · intro x hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hx
    rcases z with ⟨e,z⟩|⟨i,z⟩
    · exact Or.inl (mem_iUnion_of_mem e (subdivArc_range_subset (E e) (Q e) z hz))
    · exact Or.inr (mem_iUnion_of_mem i (subdivArc_range_subset (A i) (P i) z.val hz))

include hQ₀ hQ₁ in
lemma refinement_old_mark_vertex (e : ι) {t : I} (ht : t∈Q e) :
    Vertex (refinementArc E A P Q) (E e t) := by
  obtain ⟨z,hz⟩ := subdivision_mark_vertex (E e) (Q e) (hQ₀ e) (hQ₁ e) ht
  exact ⟨Sum.inl ⟨e,z⟩,hz⟩

include hmark hP₀ hP₁ hQ₀ hQ₁ in
lemma refinement_new_mark_vertex (i : κ) {t : I} (ht : t∈P i) :
    Vertex (refinementArc E A P Q) (A i t) := by
  classical
  by_cases h : ∃ e, A i t∈range (E e)
  · obtain ⟨e,w,hw⟩ := h
    rw [← hw]
    apply refinement_old_mark_vertex E A P Q hQ₀ hQ₁ e
    exact hmark i e w ⟨t,ht,hw.symm⟩
  · obtain ⟨z,hz⟩ := subdivision_mark_vertex (A i) (P i) (hP₀ i) (hP₁ i) ht
    have hf : FreeSegment E A P i z := by
      intro e he
      apply h
      refine ⟨e,he ?_⟩
      rcases hz with hz|hz
      · exact ⟨0,hz⟩
      · exact ⟨1,hz⟩
    exact ⟨Sum.inr ⟨i,⟨z,hf⟩⟩,hz⟩

lemma refinement_card [Fintype ι] [Fintype κ] : Fintype.card (RefinementIndex E A P Q) ≤
    (∑ e, (Q e).card^2)+(∑ i, (P i).card^2) := by
  classical
  unfold RefinementIndex
  rw [Fintype.card_sum,Fintype.card_sigma,Fintype.card_sigma]
  apply Nat.add_le_add
  · exact Finset.sum_le_sum (fun e _ => by
      simpa only [Fintype.card_coe] using segments_card (Q e))
  · apply Finset.sum_le_sum
    intro i _
    exact (Fintype.card_subtype_le _).trans (by
      simpa only [Fintype.card_coe] using segments_card (P i))

end Arc
end CannonEmbeddedArc

namespace CannonEmbeddedArc
open Set unitInterval
open scoped BigOperators

namespace Arc
variable {X : Type*} [TopologicalSpace X]

lemma range_subset_of_interior {S : Set X} (hS : IsClosed S) (a : Arc X)
    (h : ∀ t : I, t≠0 → t≠1 → a t∈S) : range a ⊆ S := by
  have hc : closure (Ioo (0 : I) 1) ⊆ a ⁻¹' S :=
    (hS.preimage a.continuous).closure_subset_iff.mpr
      (fun t ht => h t (ne_of_gt ht.1) (ne_of_lt ht.2))
  rintro _ ⟨t,rfl⟩
  apply hc
  rw [closure_Ioo (show (0 : I)≠1 from zero_ne_one)]
  exact ⟨unitInterval.nonneg t,unitInterval.le_one t⟩

lemma free_segment_original [T2Space X] {ι : Type*} (E : ι → Arc X)
    (a b : Arc X) (P : Finset I) (z : segments P)
    (hinterval : ∀ e, (b ⁻¹' range (E e))=∅ ∨
      ∃ u∈P, ∃ v∈P, u≤v ∧ b ⁻¹' range (E e)=Icc u v)
    (hfree : ∀ e, ¬range (subdivArc b P z) ⊆ range (E e))
    (hsupp : ∀ x∈range b, x∈range a ∨ ∃ e, x∈range (E e)) :
    range (subdivArc b P z) ⊆ range a := by
  apply range_subset_of_interior a.compact_range.isClosed
  intro t ht₀ ht₁
  rcases hsupp _ (subdivArc_range_subset b P z (mem_range_self t)) with h|⟨e,he⟩
  · exact h
  · obtain h|h := (free_segment_intersection (segment_consecutive P z)
      (hinterval e) (hfree e)).1 t he
    · exact (ht₀ h).elim
    · exact (ht₁ h).elim

noncomputable def intersectionCount {ι : Type*} [Fintype ι] (E : ι → Arc X) (S : Set X) : ℕ := by
  classical
  exact ∑ i, if (range (E i) ∩ S).Nonempty then 1 else 0

lemma intersectionCount_eq_card {ι : Type*} [Fintype ι] (E : ι → Arc X) (S : Set X) :
    intersectionCount E S = by classical exact (Finset.univ.filter
      (fun i => (range (E i) ∩ S).Nonempty)).card := by
  classical
  simp only [intersectionCount,Finset.sum_boole,Nat.cast_id]

lemma sum_indicator_le_card {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (∑ i, if p i then 1 else 0) ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = _ := by simp

lemma refinement_local_count {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → Arc X) (A B : κ → Arc X) (P : κ → Finset I) (Q : ι → Finset I)
    (hsource : ∀ i z, FreeSegment E A P i z → range (subdivArc (A i) (P i) z) ⊆ range (B i))
    (p q : ℕ) (hP : ∀ i, (P i).card≤p) (hQ : ∀ e, (Q e).card≤q) (S : Set X) :
    intersectionCount (refinementArc E A P Q) S ≤
      intersectionCount E S*q^2 + intersectionCount B S*p^2 := by
  classical
  unfold intersectionCount
  change (∑ z : (Σ e : ι, segments (Q e)) ⊕
    (Σ i : κ, {z : segments (P i) // FreeSegment E A P i z}),
    if (range (refinementArc E A P Q z) ∩ S).Nonempty then 1 else 0) ≤ _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma]
  apply Nat.add_le_add
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    by_cases he : (range (E e) ∩ S).Nonempty
    · simp only [he,ite_true,one_mul]
      calc
        _ ≤ Fintype.card (segments (Q e)) := sum_indicator_le_card _
        _ = (segments (Q e)).card := Fintype.card_coe _
        _ ≤ (Q e).card^2 := segments_card _
        _ ≤ q^2 := Nat.pow_le_pow_left (hQ e) 2
    · simp only [he,ite_false,zero_mul]
      apply Nat.le_zero.mpr
      apply Finset.sum_eq_zero
      intro z _
      apply ite_eq_right
      rintro ⟨x,hx,hS⟩
      exact he ⟨x,subdivArc_range_subset (E e) (Q e) z hx,hS⟩
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (range (B i) ∩ S).Nonempty
    · simp only [hi,ite_true,one_mul]
      calc
        _ ≤ Fintype.card {z : segments (P i) // FreeSegment E A P i z} := sum_indicator_le_card _
        _ ≤ Fintype.card (segments (P i)) := Fintype.card_subtype_le _
        _ = (segments (P i)).card := Fintype.card_coe _
        _ ≤ (P i).card^2 := segments_card _
        _ ≤ p^2 := Nat.pow_le_pow_left (hP i) 2
    · simp only [hi,ite_false,zero_mul]
      apply Nat.le_zero.mpr
      apply Finset.sum_eq_zero
      intro z _
      apply ite_eq_right
      rintro ⟨x,hx,hS⟩
      exact hi ⟨x,hsource i z.val z.property hx,hS⟩

end Arc
end CannonEmbeddedArc

end
end
end
end
end

end OAI
