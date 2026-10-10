import Mathlib
import OAI.GroupTheory.FiniteType.OrderChainsExactSubtypeOfExactSet

namespace OAI

section
noncomputable section
open scoped commutatorElement
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace PartitionMaps
variable {I : Type} [Fintype I]

def equiv (p : I → Prefix S) (hp : IsPartition p) : I × Box S ≃ Box S :=
  Equiv.ofBijective (fun z => (p z.1).chart z.2) (by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ he
      have hij : i=j := (hp ((p i).chart x)).unique ⟨x,rfl⟩ ⟨y,he.symm⟩
      subst j
      exact Prod.ext rfl ((p i).chart_injective he)
    · intro x
      obtain ⟨i,⟨y,hy⟩,_⟩ := hp x
      exact ⟨(i,y),hy⟩)

omit [Fintype I] in
@[simp] lemma equiv_apply [Fintype I] (p : I → Prefix S) (hp : IsPartition p) (i : I) (x : Box S) :
    equiv p hp (i,x) = (p i).chart x := rfl

def rearrange (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q) : localGroup ρ :=
  ⟨(equiv p hp).symm.trans (equiv q hq),by
    intro x
    obtain ⟨i,hix,_⟩ := hp x
    refine ⟨p i,q i,1,hix,?_⟩
    intro y
    change equiv q hq ((equiv p hp).symm (equiv p hp (i,y))) = _
    rw [Equiv.symm_apply_apply,twist_one]
    rfl⟩

omit [Fintype I] in
@[simp] lemma rearrange_chart [Fintype I] (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q)
    (i : I) (x : Box S) :
    (rearrange ρ p q hp hq).val ((p i).chart x) = (q i).chart x :=
  congrArg (equiv q hq) ((equiv p hp).symm_apply_apply (i,x))

def pieces (p : I → Prefix S) (hp : IsPartition p) (g : I → localGroup ρ) : localGroup ρ :=
  ⟨(equiv p hp).symm.trans ((Equiv.prodCongrRight fun i => (g i).val).trans (equiv p hp)),by
    apply locallyStandard_of_charts ρ (fun i => LocalEmbedding.ofPrefix ρ (p i))
      (fun i => LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ (p i)) (LocalEmbedding.ofGroup ρ (g i)))
    · intro x
      obtain ⟨i,⟨y,hy⟩,_⟩ := hp x
      exact ⟨i,y,hy⟩
    · intro i y
      change equiv p hp ((Equiv.prodCongrRight fun i => (g i).val)
        ((equiv p hp).symm (equiv p hp (i,y)))) = _
      rw [Equiv.symm_apply_apply]
      rfl⟩

omit [Fintype I] in
@[simp] lemma pieces_chart [Fintype I] (p : I → Prefix S) (hp : IsPartition p)
    (g : I → localGroup ρ) (i : I) (x : Box S) :
    (pieces ρ p hp g).val ((p i).chart x) = (p i).chart ((g i).val x) := by
  change equiv p hp ((Equiv.prodCongrRight fun i => (g i).val)
    ((equiv p hp).symm (equiv p hp (i,x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

omit [Fintype I] in
lemma ext [Fintype I] (p : I → Prefix S) (hp : IsPartition p) {g h : localGroup ρ}
    (he : ∀ i x, g.val ((p i).chart x) = h.val ((p i).chart x)) : g=h := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨i,⟨y,rfl⟩,_⟩ := hp x
  exact he i y

def piecesHom (p : I → Prefix S) (hp : IsPartition p) : (I → localGroup ρ) →* localGroup ρ where
  toFun := pieces ρ p hp
  map_one' := by
    apply ext ρ p hp
    intro i x
    simp only [pieces_chart,Pi.one_apply,OneMemClass.coe_one,Equiv.Perm.one_apply]
  map_mul' g h := by
    apply ext ρ p hp
    intro i x
    simp only [pieces_chart,Pi.mul_apply,Subgroup.coe_mul,Equiv.Perm.mul_apply]

@[simp] lemma piecesHom_apply (p : I → Prefix S) (hp : IsPartition p)
    (g : I → localGroup ρ) : piecesHom ρ p hp g=pieces ρ p hp g := rfl

lemma piecesHom_injective (p : I → Prefix S) (hp : IsPartition p) :
    Function.Injective (piecesHom ρ p hp) := by
  intro g h he
  funext i
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply (p i).chart_injective
  simpa only [piecesHom,MonoidHom.coe_mk,OneHom.coe_mk,pieces_chart] using
    congrArg (fun k : localGroup ρ => k.val ((p i).chart x)) he

end PartitionMaps
namespace Prefix

lemma grid_of_chart (p : Prefix S) (x : Box S) :
    gridPrefix p.lengths (gridPoint p.lengths (p.chart x)) = p := by
  apply Prefix.ext
  intro s
  apply List.ext_getElem
  · simp [gridPrefix_length]
  · intro n hn hm
    have hz := (mem_brick_iff_get _ _).mp (mem_gridPrefix p.lengths (p.chart x)) s n hn
    have hp := (mem_brick_iff_get p _).mp (chart_mem_brick p x) s n hm
    exact hz.symm.trans hp

end Prefix
namespace Localization

noncomputable def gridIndex (p : Prefix S) : Prefix.Grid p.lengths :=
  Prefix.gridPoint p.lengths (p.chart (fun _ _ => false))

lemma gridIndex_prefix (p : Prefix S) : Prefix.gridPrefix p.lengths (gridIndex p) = p :=
  Prefix.grid_of_chart p _

def hom (p : Prefix S) : localGroup ρ →* localGroup ρ := by
  classical
  exact (PartitionMaps.piecesHom ρ (Prefix.gridPrefix p.lengths) (Prefix.grid_partition _)).comp
    (MonoidHom.mulSingle (fun _ : Prefix.Grid p.lengths => localGroup ρ) (gridIndex p))

lemma chart (p : Prefix S) (g : localGroup ρ) (x : Box S) :
    (hom ρ p g).val (p.chart x) = p.chart (g.val x) := by
  classical
  conv_lhs => arg 2; rw [← gridIndex_prefix p]
  change (PartitionMaps.pieces ρ _ _ (Pi.mulSingle (gridIndex p) g)).val _ = _
  rw [PartitionMaps.pieces_chart,Pi.mulSingle_eq_same,gridIndex_prefix]

lemma outside (p : Prefix S) (g : localGroup ρ) (x : Box S) (hx : x ∉ p.brick) :
    (hom ρ p g).val x = x := by
  classical
  obtain ⟨i,⟨y,hy⟩,_⟩ := Prefix.grid_partition p.lengths x
  have hi : i ≠ gridIndex p := by
    intro hi
    subst i
    rw [gridIndex_prefix] at hy
    exact hx ⟨y,hy⟩
  rw [← hy]
  change (PartitionMaps.pieces ρ _ _ (Pi.mulSingle (gridIndex p) g)).val _ = _
  rw [PartitionMaps.pieces_chart,Pi.mulSingle_eq_of_ne hi]
  rfl

lemma injective (p : Prefix S) : Function.Injective (hom ρ p) := by
  intro g h he
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply p.chart_injective
  simpa only [chart] using congrArg (fun k : localGroup ρ => k.val (p.chart x)) he

end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix
lemma disjoint_of_length {p q : Prefix S} {x : Box S} (hx : x ∈ q.brick)
    (hn : x ∉ p.brick) (hl : ∀ s, (p s).length ≤ (q s).length) : Disjoint p.brick q.brick := by
  apply Set.disjoint_left.mpr
  intro y hy hyq
  exact hn (brick_subset_of_extends (extends_of_mem_of_length_le hy hyq hl) hx)
end Prefix
namespace BrickSwap
variable (p q : Prefix S) (hd : Disjoint p.brick q.brick)

def fn (x : Box S) : Box S := by
  classical
  exact if x ∈ p.brick then q.chart (p.tail x)
  else if x ∈ q.brick then p.chart (q.tail x) else x

lemma chart_left (x : Box S) : fn p q (p.chart x) = q.chart x := by
  simp only [fn,Prefix.chart_mem_brick,ite_true,Prefix.tail_chart]

include hd in
lemma chart_right (x : Box S) : fn p q (q.chart x) = p.chart x := by
  have hn : q.chart x ∉ p.brick := fun hp => (Set.disjoint_left.mp hd) hp (Prefix.chart_mem_brick _ _)
  simp only [fn,hn,ite_false,Prefix.chart_mem_brick,ite_true,Prefix.tail_chart]

lemma outside (x : Box S) (hp : x ∉ p.brick) (hq : x ∉ q.brick) : fn p q x=x := by
  simp [fn,hp,hq]

include hd in
lemma involutive : Function.Involutive (fn p q) := by
  intro x
  by_cases hp : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hp
    rw [chart_left,chart_right p q hd]
  · by_cases hq : x ∈ q.brick
    · obtain ⟨y,rfl⟩ := hq
      rw [chart_right p q hd,chart_left]
    · rw [outside p q x hp hq,outside p q x hp hq]

def elem : localGroup ρ :=
  ⟨(involutive p q hd).toPerm,by
    intro x
    by_cases hp : x ∈ p.brick
    · exact ⟨p,q,1,hp,by intro y; change fn p q _ = _; rw [chart_left,twist_one]⟩
    by_cases hq : x ∈ q.brick
    · exact ⟨q,p,1,hq,by intro y; change fn p q _ = _; rw [chart_right p q hd,twist_one]⟩
    let b := p.lengths + q.lengths
    let r := Prefix.gridPrefix b (Prefix.gridPoint b x)
    have hr : x ∈ r.brick := Prefix.mem_gridPrefix b x
    have hpr : Disjoint p.brick r.brick := Prefix.disjoint_of_length hr hp (by
      intro s
      simp [r,b,Prefix.gridPrefix_length])
    have hqr : Disjoint q.brick r.brick := Prefix.disjoint_of_length hr hq (by
      intro s
      simp [r,b,Prefix.gridPrefix_length])
    refine ⟨r,r,1,hr,?_⟩
    intro y
    change fn p q (r.chart y) = _
    rw [outside p q _ (fun hh => Set.disjoint_left.mp hpr hh (Prefix.chart_mem_brick _ _))
      (fun hh => Set.disjoint_left.mp hqr hh (Prefix.chart_mem_brick _ _)),twist_one]⟩

@[simp] lemma elem_apply (x : Box S) : (elem ρ p q hd).val x=fn p q x := rfl

@[simp] lemma elem_left (x : Box S) : (elem ρ p q hd).val (p.chart x)=q.chart x := chart_left p q x
@[simp] lemma elem_right (x : Box S) : (elem ρ p q hd).val (q.chart x)=p.chart x := chart_right p q hd x

lemma elem_sq : elem ρ p q hd * elem ρ p q hd=1 := by
  apply Subtype.ext
  exact Equiv.ext (involutive p q hd)

lemma elem_inv : (elem ρ p q hd)⁻¹=elem ρ p q hd := inv_eq_of_mul_eq_one_left (elem_sq ρ p q hd)

end BrickSwap
namespace Localization

lemma apply_mem_iff (p : Prefix S) (g : localGroup ρ) (x : Box S) :
    (hom ρ p g).val x ∈ p.brick ↔ x ∈ p.brick := by
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [chart]
    exact iff_of_true (Prefix.chart_mem_brick _ _) (Prefix.chart_mem_brick _ _)
  · rw [outside ρ p g x hx]

lemma conjugate (p q : Prefix S) (h g : localGroup ρ)
    (he : ∀ x, h.val (p.chart x)=q.chart x) :
    h * hom ρ p g * h⁻¹ = hom ρ q g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := h.val.surjective x
  change h.val ((hom ρ p g).val (h.val.symm (h.val y))) = _
  rw [h.val.symm_apply_apply]
  by_cases hp : y ∈ p.brick
  · obtain ⟨z,rfl⟩ := hp
    rw [chart,he,he,chart]
  · have hq : h.val y ∉ q.brick := by
      rintro ⟨z,hz⟩
      exact hp ⟨z,h.val.injective ((he z).trans hz)⟩
    rw [outside ρ p g y hp,outside ρ q g _ hq]

lemma conjugate_swap (p q : Prefix S) (hd : Disjoint p.brick q.brick) (g : localGroup ρ) :
    BrickSwap.elem ρ p q hd * hom ρ p g * (BrickSwap.elem ρ p q hd)⁻¹ = hom ρ q g :=
  conjugate ρ p q _ g (BrickSwap.elem_left ρ p q hd)

lemma append (p q : Prefix S) (g : localGroup ρ) :
    hom ρ (p.append q) g = hom ρ p (hom ρ q g) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [chart]
    by_cases hy : y ∈ q.brick
    · obtain ⟨z,rfl⟩ := hy
      rw [← Prefix.chart_append,chart,Prefix.chart_append,chart]
    · have hxy : p.chart y ∉ (p.append q).brick := by
        rintro ⟨z,hz⟩
        rw [Prefix.chart_append] at hz
        exact hy ⟨z,p.chart_injective hz⟩
      rw [outside ρ (p.append q) g _ hxy,outside ρ q g _ hy]
  · have hxy : x ∉ (p.append q).brick := fun hh => hx (Prefix.brick_append_subset p q hh)
    rw [outside ρ (p.append q) g x hxy,outside ρ p _ x hx]

end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix
lemma exists_disjoint {p : Prefix S} (hp : p ≠ empty) :
    ∃ q : Prefix S, Disjoint p.brick q.brick := by
  classical
  have hn : p.brick ≠ Set.univ := fun h => hp (eq_empty_of_brick_univ h)
  obtain ⟨x,hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hn
  exact ⟨gridPrefix p.lengths (gridPoint p.lengths x),
    disjoint_of_length (mem_gridPrefix p.lengths x) hx (by intro s; rw [gridPrefix_length]; exact le_rfl)⟩

lemma cut_partition (s : S) : IsPartition (cut s) := by
  intro x
  refine ⟨(x s).get 0, (mem_cut_iff s _ x).mpr rfl, ?_⟩
  intro b hb
  exact ((mem_cut_iff s b x).mp hb).symm

lemma cut_ne_empty (s : S) (b : Bool) : cut s b ≠ empty := by
  intro h
  have := congrArg (fun p : Prefix S => p s) h
  simp at this

lemma append_ne_empty_left {p : Prefix S} (hp : p ≠ empty) (q : Prefix S) :
    p.append q ≠ empty := by
  intro h
  apply hp
  apply Prefix.ext
  intro s
  have hh := congrArg (fun p : Prefix S => p s) h
  exact (List.append_eq_nil_iff.mp hh).1

lemma chart_cut_commute (p : Prefix S) (s : S) (hp : p s = []) (b : Bool) (x : Box S) :
    p.chart ((cut s b).chart x) = (cut s b).chart (p.chart x) := by
  classical
  rw [← chart_append,← chart_append]
  congr 1
  apply Prefix.ext
  intro t
  by_cases ht : t=s
  · subst t; simp [append_apply,hp]
  · simp [append_apply,cut_apply,ht]

lemma mem_cut_chart_iff (p : Prefix S) (s : S) (hp : p s=[]) (b : Bool) (x : Box S) :
    (cut s b).chart x ∈ p.brick ↔ x ∈ p.brick := by
  rw [mem_brick_iff_get,mem_brick_iff_get]
  constructor <;> intro h t n hn
  · by_cases ht : t=s
    · subst t; simp [hp] at hn
    · simpa [chart,cut_apply,ht] using h t n hn
  · by_cases ht : t=s
    · subst t; simp [hp] at hn
    · simpa [chart,cut_apply,ht] using h t n hn
end Prefix
namespace Localization
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)

lemma image_eq_of_disjoint (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
    {p q : Prefix S} (hd : Disjoint p.brick q.brick) (g : localGroup ρ) :
    π (hom ρ p g)=π (hom ρ q g) := by
  have h := congrArg π (conjugate_swap ρ p q hd g)
  rw [map_mul,map_mul,map_inv] at h
  rw [(hc p q hd (hom ρ p g)).eq, mul_assoc,mul_inv_cancel,mul_one] at h
  exact h

lemma image_eq_proper (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
    {p q : Prefix S} (hp : p ≠ Prefix.empty) (hq : q ≠ Prefix.empty) (g : localGroup ρ) :
    π (hom ρ p g)=π (hom ρ q g) := by
  classical
  obtain ⟨r,hpr⟩ := Prefix.exists_disjoint hp
  obtain ⟨u,hqu⟩ := Prefix.exists_disjoint hq
  by_cases hrq : Disjoint r.brick q.brick
  · exact (image_eq_of_disjoint ρ π hc hpr g).trans (image_eq_of_disjoint ρ π hc hrq g)
  · obtain ⟨x,hxr,hxq⟩ := Set.not_disjoint_iff.mp hrq
    let v := Prefix.common x r q
    have hvr : v.brick ⊆ r.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_left hxr)
    have hvq : v.brick ⊆ q.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_right hxq)
    exact (image_eq_of_disjoint ρ π hc (hpr.mono_right hvr) g).trans
      ((image_eq_of_disjoint ρ π hc (hqu.mono_left hvq) g).trans
        (image_eq_of_disjoint ρ π hc hqu.symm g))
end Localization

def Stationary (s : S) (g : localGroup ρ) : Prop :=
  ∀ b x, g.val ((Prefix.cut s b).chart x) = (Prefix.cut s b).chart (g.val x)

namespace Stationary
lemma split {s : S} {g : localGroup ρ} (hg : Stationary ρ s g) :
    g = Localization.hom ρ (Prefix.cut s false) g * Localization.hom ρ (Prefix.cut s true) g := by
  apply PartitionMaps.ext ρ (Prefix.cut s) (Prefix.cut_partition s)
  intro b x
  change g.val _ = (Localization.hom ρ _ g).val ((Localization.hom ρ _ g).val _)
  cases b
  · have hn : (Prefix.cut s false).chart x ∉ (Prefix.cut s true).brick := by
      intro hh
      exact Bool.false_ne_true (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ x) hh))
    rw [Localization.outside ρ _ g _ hn,Localization.chart,hg]
  · rw [Localization.chart]
    have hn : (Prefix.cut s true).chart (g.val x) ∉ (Prefix.cut s false).brick := by
      intro hh
      exact Bool.noConfusion (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ (g.val x)) hh))
    rw [Localization.outside ρ _ g _ hn,hg]

lemma localize {s : S} {g : localGroup ρ} (hg : Stationary ρ s g)
    (p : Prefix S) (hp : p s=[]) : Stationary ρ s (Localization.hom ρ p g) := by
  intro b x
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [← Prefix.chart_cut_commute p s hp,Localization.chart,hg,
      Prefix.chart_cut_commute p s hp,Localization.chart]
  · rw [Localization.outside ρ p g x hx,
      Localization.outside ρ p g _ (fun h => hx ((Prefix.mem_cut_chart_iff p s hp b x).mp h))]
end Stationary
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Stationary
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc

lemma local_image_eq_one {s : S} {g : localGroup ρ} (hg : Stationary ρ s g)
    {p : Prefix S} (hp : p ≠ Prefix.empty) : π (Localization.hom ρ p g)=1 := by
  have hh := congrArg (fun k => π (Localization.hom ρ p k)) (split ρ hg)
  rw [map_mul,map_mul,← Localization.append,← Localization.append] at hh
  rw [Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp,
    Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp] at hh
  exact (mul_eq_left.mp hh.symm)

lemma image_eq_one {s : S} {g : localGroup ρ} (hg : Stationary ρ s g) : π g=1 := by
  rw [split ρ hg,map_mul,local_image_eq_one ρ π hc hg (Prefix.cut_ne_empty _ _),
    local_image_eq_one ρ π hc hg (Prefix.cut_ne_empty _ _),one_mul]
end Stationary
namespace PartitionMaps
variable {I : Type} [Fintype I]
lemma stationary_rearrange (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q)
    {s : S} (hs : ∀ i, p i s=[] ∧ q i s=[]) :
    Stationary ρ s (rearrange ρ p q hp hq) := by
  intro b x
  obtain ⟨i,⟨y,rfl⟩,_⟩ := hp x
  rw [← Prefix.chart_cut_commute (p i) s (hs i).1,
    rearrange_chart,rearrange_chart,Prefix.chart_cut_commute (q i) s (hs i).2]

lemma fresh [Infinite S] (p q : I → Prefix S) (r : Prefix S) :
    ∃ s : S, r s=[] ∧ ∀ i, p i s=[] ∧ q i s=[] := by
  classical
  have hf := ((Set.finite_iUnion fun i => (p i).finite_support).union
    (Set.finite_iUnion fun i => (q i).finite_support)).union r.finite_support
  obtain ⟨s,hs⟩ := hf.exists_notMem
  simp only [Set.mem_union,Set.mem_iUnion,Set.mem_ofPred_eq,not_or,not_exists,not_not] at hs
  exact ⟨s,hs.2,fun i => ⟨hs.1.1 i,hs.1.2 i⟩⟩

variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc

lemma rearrange_image [Infinite S] (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q) :
    π (rearrange ρ p q hp hq)=1 := by
  obtain ⟨s,_,hs⟩ := fresh p q Prefix.empty
  exact Stationary.image_eq_one ρ π hc (stationary_rearrange ρ p q hp hq hs)

lemma rearrange_local_image [Infinite S] (p q : I → Prefix S) (hp : IsPartition p)
    (hq : IsPartition q) (r : Prefix S) : π (Localization.hom ρ r (rearrange ρ p q hp hq))=1 := by
  obtain ⟨s,hr,hs⟩ := fresh p q r
  exact Stationary.image_eq_one ρ π hc
    (Stationary.localize ρ (stationary_rearrange ρ p q hp hq hs) r hr)
end PartitionMaps
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Localization
lemma cuts_chart (s : S) (g : localGroup ρ) (b : Bool) (x : Box S) :
    (hom ρ (Prefix.cut s false) g * hom ρ (Prefix.cut s true) g).val
      ((Prefix.cut s b).chart x) = (Prefix.cut s b).chart (g.val x) := by
  change (hom ρ _ g).val ((hom ρ _ g).val _) = _
  cases b
  · have hn : (Prefix.cut s false).chart x ∉ (Prefix.cut s true).brick := by
      intro hh
      exact Bool.false_ne_true (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ x) hh))
    rw [outside ρ _ g _ hn,chart]
  · rw [chart]
    have hn : (Prefix.cut s true).chart (g.val x) ∉ (Prefix.cut s false).brick := by
      intro hh
      exact Bool.noConfusion (((Prefix.cut_partition s _).unique
        (Prefix.chart_mem_brick _ (g.val x)) hh))
    rw [outside ρ _ g _ hn]

@[simp] lemma empty (g : localGroup ρ) : hom ρ Prefix.empty g=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact chart ρ Prefix.empty g x
end Localization

lemma global_split (a : A) (s : S) :
    globalHom ρ a =
      PartitionMaps.rearrange ρ (Prefix.cut s) (Prefix.cut (ρ a s))
        (Prefix.cut_partition s) (Prefix.cut_partition (ρ a s)) *
      (Localization.hom ρ (Prefix.cut s false) (globalHom ρ a) *
        Localization.hom ρ (Prefix.cut s true) (globalHom ρ a)) := by
  apply PartitionMaps.ext ρ (Prefix.cut s) (Prefix.cut_partition s)
  intro b x
  change twist ρ a _ = _
  rw [twist_chart,Prefix.permute_cut]
  simp only [Subgroup.coe_mul,Equiv.Perm.mul_apply]
  rw [show (Localization.hom ρ (Prefix.cut s false) (globalHom ρ a)).val
      ((Localization.hom ρ (Prefix.cut s true) (globalHom ρ a)).val ((Prefix.cut s b).chart x)) =
      (Prefix.cut s b).chart ((globalHom ρ a).val x) from Localization.cuts_chart ρ s _ b x,
    PartitionMaps.rearrange_chart]
  rfl

namespace PerfectProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc
lemma global_local_image [Infinite S] (a : A) {p : Prefix S} (hp : p ≠ Prefix.empty) :
    π (Localization.hom ρ p (globalHom ρ a))=1 := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  have hh := congrArg (fun g => π (Localization.hom ρ p g)) (global_split ρ a s)
  rw [map_mul,map_mul,map_mul,map_mul,PartitionMaps.rearrange_local_image ρ π hc,
    one_mul,← Localization.append,← Localization.append] at hh
  rw [Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp,
    Localization.image_eq_proper ρ π hc (Prefix.append_ne_empty_left hp _) hp] at hh
  exact mul_eq_left.mp hh.symm

lemma global_image [Infinite S] (a : A) : π (globalHom ρ a)=1 := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  rw [global_split ρ a s,map_mul,map_mul,PartitionMaps.rearrange_image ρ π hc,
    global_local_image ρ π hc a (Prefix.cut_ne_empty _ _),
    global_local_image ρ π hc a (Prefix.cut_ne_empty _ _),one_mul,one_mul]

lemma global_local_image_all [Infinite S] (a : A) (p : Prefix S) :
    π (Localization.hom ρ p (globalHom ρ a))=1 := by
  by_cases hp : p=Prefix.empty
  · subst p; rw [Localization.empty]; exact global_image ρ π hc a
  · exact global_local_image ρ π hc a hp
end PerfectProducer
namespace PartitionMaps
variable {I : Type} [Fintype I]
lemma pieces_mulSingle [DecidableEq I] (p : I → Prefix S) (hp : IsPartition p)
    (i : I) (g : localGroup ρ) :
    pieces ρ p hp (Pi.mulSingle i g) = Localization.hom ρ (p i) g := by
  apply ext ρ p hp
  intro j x
  rw [pieces_chart]
  by_cases hj : j=i
  · subst j; rw [Pi.mulSingle_eq_same,Localization.chart]
  · rw [Pi.mulSingle_eq_of_ne hj]
    have hn : (p j).chart x ∉ (p i).brick := fun hh =>
      hj ((hp _).unique (Prefix.chart_mem_brick _ _) hh)
    rw [Localization.outside ρ _ g _ hn]
    rfl
end PartitionMaps
namespace PerfectProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)
variable (hc : ∀ p q hd (g : localGroup ρ),
    Commute (π (BrickSwap.elem ρ p q hd)) (π g))
include hc
lemma pieces_global_image [Infinite S] {I : Type} [Fintype I]
    (p : I → Prefix S) (hp : IsPartition p) (a : I → A) :
    π (PartitionMaps.pieces ρ p hp (fun i => globalHom ρ (a i)))=1 := by
  classical
  let f : (I → A) →* Q :=
    (π.comp (PartitionMaps.piecesHom ρ p hp)).comp (MonoidHom.piMap fun _ : I => globalHom ρ)
  have hf : f=1 := by
    apply MonoidHom.pi_ext
    intro i b
    simp only [f,MonoidHom.comp_apply,MonoidHom.one_apply,PartitionMaps.piecesHom_apply]
    change π (PartitionMaps.pieces ρ p hp (fun j : I => globalHom ρ ((Pi.mulSingle i b : I → A) j))) = 1
    have he : (fun j : I => globalHom ρ ((Pi.mulSingle i b : I → A) j))=(Pi.mulSingle i (globalHom ρ b) : I → localGroup ρ) := by
      funext j
      by_cases hj : j=i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [he,PartitionMaps.pieces_mulSingle,global_local_image_all ρ π hc]
  exact DFunLike.congr_fun hf a

lemma hom_eq_one [Infinite S] (g : localGroup ρ) : π g=1 := by
  obtain ⟨T,hT⟩ := hasTable_of_isLocal ρ g.property
  have he : g = PartitionMaps.rearrange ρ T.dom T.ran T.dom_partition T.ran_partition *
      PartitionMaps.pieces ρ T.dom T.dom_partition (fun i => globalHom ρ (T.label i)) := by
    apply PartitionMaps.ext ρ T.dom T.dom_partition
    intro i x
    change g.val ((T.dom i).chart x) =
      (PartitionMaps.rearrange ρ T.dom T.ran T.dom_partition T.ran_partition).val
      ((PartitionMaps.pieces ρ T.dom T.dom_partition (fun i => globalHom ρ (T.label i))).val
        ((T.dom i).chart x))
    rw [PartitionMaps.pieces_chart,PartitionMaps.rearrange_chart]
    exact hT i x
  rw [he,map_mul,PartitionMaps.rearrange_image ρ π hc,pieces_global_image ρ π hc,one_mul]

end PerfectProducer
lemma localGroup_perfect [Infinite S] : Group.IsPerfect (localGroup ρ) := by
  constructor
  rw [← Abelianization.ker_of]
  apply top_unique
  intro g _
  exact PerfectProducer.hom_eq_one ρ Abelianization.of (fun _ _ _ _ => Commute.all _ _) g
end TwistedBrin

end
end

end OAI
