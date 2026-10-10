import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinEquiv

namespace OAI

section
noncomputable section
open scoped commutatorElement
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix
lemma separated {x y : Box S} (hxy : x ≠ y) :
    ∃ p q : Prefix S, x ∈ p.brick ∧ y ∈ q.brick ∧ Disjoint p.brick q.brick := by
  classical
  have hh : ∃ s n, (x s).get n ≠ (y s).get n := by
    contrapose! hxy
    funext s n
    exact hxy s n
  obtain ⟨s,n,hn⟩ := hh
  let b := Finsupp.single s (n+1)
  let p := gridPrefix b (gridPoint b x)
  let q := gridPrefix b (gridPoint b y)
  have hp := mem_gridPrefix b x
  have hq := mem_gridPrefix b y
  refine ⟨p,q,hp,hq,Set.disjoint_left.mpr ?_⟩
  intro z hz hzq
  have hnp : n < (p s).length := by simp [p,gridPrefix_length,b]
  have hnq : n < (q s).length := by simp [q,gridPrefix_length,b]
  exact hn (((mem_brick_iff_get p x).mp hp s n hnp).trans
    (((mem_brick_iff_get p z).mp hz s n hnp).symm.trans
      (((mem_brick_iff_get q z).mp hzq s n hnq).trans
        ((mem_brick_iff_get q y).mp hq s n hnq).symm)))
end Prefix

lemma exists_displaced_brick {g : localGroup ρ} (hg : g ≠ 1) :
    ∃ (p q : Prefix S) (a : A), Disjoint p.brick q.brick ∧
      ∀ y, g.val (p.chart y)=q.chart (twist ρ a y) := by
  classical
  have hx : ∃ x : Box S, g.val x ≠ x := by
    by_contra hh
    push Not at hh
    apply hg
    apply Subtype.ext
    exact Equiv.ext hh
  obtain ⟨x,hx⟩ := hx
  obtain ⟨R,T,hxR,hxT,hRT⟩ := Prefix.separated hx.symm
  obtain ⟨u,v,a,hxu,he⟩ := g.property x
  let p := Prefix.common x u R
  let c := u.suffix p
  let q := v.append (c.permute (ρ a))
  have huc : u.append c=p := Prefix.append_suffix (Prefix.extends_common_left hxu)
  have hp : x ∈ p.brick := Prefix.mem_common _ _ _
  have hep (y : Box S) : g.val (p.chart y)=q.chart (twist ρ a y) := by
    rw [← huc,Prefix.chart_append,he,twist_chart,← Prefix.chart_append]
  have hq : g.val x ∈ q.brick := by
    obtain ⟨y,hy⟩ := hp
    exact ⟨twist ρ a y,by rw [← hep,hy]⟩
  let z := Prefix.common (g.val x) q T
  let d := q.suffix z
  let P := p.append (d.permute (ρ a⁻¹))
  have hqd : q.append d=z := Prefix.append_suffix (Prefix.extends_common_left hq)
  have heP (y : Box S) : g.val (P.chart y)=z.chart (twist ρ a y) := by
    change g.val ((p.append (d.permute (ρ a⁻¹))).chart y)=_
    rw [Prefix.chart_append,hep,twist_chart,twist_prefix_inv,← Prefix.chart_append,hqd]
  refine ⟨P,z,a,hRT.mono ?_ ?_,heP⟩
  · exact (Prefix.brick_append_subset p _).trans
      (Prefix.brick_subset_of_extends (Prefix.extends_common_right hxR))
  · exact Prefix.brick_subset_of_extends (Prefix.extends_common_right hxT)

namespace Localization
lemma commute_of_disjoint_support {U V : Set (Box S)} (hd : Disjoint U V)
    (g h : localGroup ρ) (hg : ∀ x, x ∉ U → g.val x=x) (hh : ∀ x, x ∉ V → h.val x=x) :
    Commute g h := by
  have hgm : ∀ x ∈ U, g.val x ∈ U := by
    intro x hx
    by_contra hn
    have he : g.val x=x := g.val.injective (hg (g.val x) hn)
    exact hn (he.symm ▸ hx)
  have hhm : ∀ x ∈ V, h.val x ∈ V := by
    intro x hx
    by_contra hn
    have he : h.val x=x := h.val.injective (hh (h.val x) hn)
    exact hn (he.symm ▸ hx)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change g.val (h.val x)=h.val (g.val x)
  by_cases hx : x ∈ U
  · rw [hh x (fun h => Set.disjoint_left.mp hd hx h),
      hh (g.val x) (fun h => Set.disjoint_left.mp hd (hgm x hx) h)]
  · by_cases hv : x ∈ V
    · rw [hg x hx,hg (h.val x) (fun h => Set.disjoint_left.mp hd h (hhm x hv))]
    · rw [hg x hx,hh x hv,hg x hx]

lemma conjugate_outside {p q : Prefix S} {a : A} {f : localGroup ρ}
    (hf : ∀ y, f.val (p.chart y)=q.chart (twist ρ a y)) (g : localGroup ρ)
    (x : Box S) (hx : x ∉ q.brick) : (f * hom ρ p g * f⁻¹).val x=x := by
  have hy : f.val.symm x ∉ p.brick := by
    rintro ⟨y,hy⟩
    apply hx
    refine ⟨twist ρ a y,?_⟩
    rw [← hf,hy,f.val.apply_symm_apply]
  change f.val ((hom ρ p g).val (f.val.symm x))=x
  rw [outside ρ p g _ hy,f.val.apply_symm_apply]
end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace BrickSwap
lemma stationary {p q : Prefix S} (hd : Disjoint p.brick q.brick) {s : S}
    (hp : p s=[]) (hq : q s=[]) : Stationary ρ s (elem ρ p q hd) := by
  intro b x
  by_cases hx : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hx
    rw [← Prefix.chart_cut_commute p s hp,elem_left,elem_left,Prefix.chart_cut_commute q s hq]
  · by_cases hxq : x ∈ q.brick
    · obtain ⟨y,rfl⟩ := hxq
      rw [← Prefix.chart_cut_commute q s hq,elem_right,elem_right,Prefix.chart_cut_commute p s hp]
    · change fn p q ((Prefix.cut s b).chart x) = (Prefix.cut s b).chart (fn p q x)
      rw [outside p q x hx hxq,outside p q _
        (fun hh => hx ((Prefix.mem_cut_chart_iff p s hp b x).mp hh))
        (fun hh => hxq ((Prefix.mem_cut_chart_iff q s hq b x).mp hh))]
end BrickSwap
namespace SimplicityProducer
variable {Q : Type*} [Group Q] (π : localGroup ρ →* Q)

def KillsBrick (p : Prefix S) : Prop := ∀ g : localGroup ρ, π (Localization.hom ρ p g)=1

lemma kills_disjoint {p q : Prefix S} (hd : Disjoint p.brick q.brick)
    (hp : KillsBrick ρ π p) : KillsBrick ρ π q := by
  intro g
  have h := congrArg π (Localization.conjugate_swap ρ p q hd g)
  rw [map_mul,map_mul,map_inv,hp g,mul_one,mul_inv_cancel] at h
  exact h.symm

lemma kills_proper {p : Prefix S} (hp : p ≠ Prefix.empty) (hk : KillsBrick ρ π p)
    {q : Prefix S} (hq : q ≠ Prefix.empty) : KillsBrick ρ π q := by
  classical
  obtain ⟨r,hpr⟩ := Prefix.exists_disjoint hp
  obtain ⟨u,hqu⟩ := Prefix.exists_disjoint hq
  by_cases hrq : Disjoint r.brick q.brick
  · exact kills_disjoint ρ π hrq (kills_disjoint ρ π hpr hk)
  · obtain ⟨x,hxr,hxq⟩ := Set.not_disjoint_iff.mp hrq
    let v := Prefix.common x r q
    have hvr : v.brick ⊆ r.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_left hxr)
    have hvq : v.brick ⊆ q.brick := Prefix.brick_subset_of_extends (Prefix.extends_common_right hxq)
    exact kills_disjoint ρ π hqu.symm
      (kills_disjoint ρ π (hqu.mono_left hvq) (kills_disjoint ρ π (hpr.mono_right hvr) hk))

lemma killed_displacer [Infinite S] {f : localGroup ρ} (hf : f ≠ 1) (hπ : π f=1) :
    ∃ p : Prefix S, p ≠ Prefix.empty ∧ KillsBrick ρ π p := by
  obtain ⟨p,q,a,hd,he⟩ := exists_displaced_brick ρ hf
  have hp : p ≠ Prefix.empty := by
    intro hh
    have hq := Prefix.chart_mem_brick q (fun _ _ => false)
    have hp : q.chart (fun _ _ => false) ∈ p.brick := by rw [hh,Prefix.brick_empty]; trivial
    exact Set.disjoint_left.mp hd hp hq
  let F := π.comp (Localization.hom ρ p)
  have hc (g h : localGroup ρ) : Commute (F g) (F h) := by
    have hcomm : Commute (f * Localization.hom ρ p g * f⁻¹) (Localization.hom ρ p h) :=
      Localization.commute_of_disjoint_support ρ hd.symm _ _
        (Localization.conjugate_outside ρ he g) (Localization.outside ρ p h)
    have hc := hcomm.map π
    simpa only [map_mul,map_inv,hπ,one_mul,mul_one,inv_one,F,MonoidHom.comp_apply] using hc
  have hk : commutator (localGroup ρ) ≤ F.ker := by
    rw [commutator_eq_closure,Subgroup.closure_le]
    rintro _ ⟨g,h,rfl⟩
    change F ⁅g,h⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_commute]
    exact hc g h
  have ht : (⊤ : Subgroup (localGroup ρ)) ≤ F.ker := by
    rw [← (localGroup_perfect ρ).commutator_eq_top]
    exact hk
  exact ⟨p,hp,fun g => ht (Subgroup.mem_top g)⟩

lemma hom_eq_one_of_kills_proper [Infinite S]
    (hk : ∀ p : Prefix S, p ≠ Prefix.empty → KillsBrick ρ π p) (g : localGroup ρ) : π g=1 := by
  apply PerfectProducer.hom_eq_one ρ π _ g
  intro p q hd h
  obtain ⟨s,_,hs⟩ := PartitionMaps.fresh (fun _ : Unit => p) (fun _ : Unit => q) Prefix.empty
  have he : π (BrickSwap.elem ρ p q hd)=1 := by
    rw [Stationary.split ρ (BrickSwap.stationary ρ hd (hs ()).1 (hs ()).2),map_mul,
      hk _ (Prefix.cut_ne_empty _ _),hk _ (Prefix.cut_ne_empty _ _),one_mul]
  rw [he]
  exact Commute.one_left _

lemma hom_eq_one_of_nontrivial_kernel [Infinite S] {f : localGroup ρ} (hf : f ≠ 1)
    (hπ : π f=1) (g : localGroup ρ) : π g=1 := by
  obtain ⟨p,hp,hk⟩ := killed_displacer ρ π hf hπ
  exact hom_eq_one_of_kills_proper ρ π (fun _ hq => kills_proper ρ π hp hk hq) g
end SimplicityProducer
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
lemma localGroup_nontrivial [Nonempty S] : Nontrivial (localGroup ρ) := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  have hd : Disjoint (Prefix.cut s false).brick (Prefix.cut s true).brick := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Bool.false_ne_true ((Prefix.cut_partition s x).unique hx hy)
  let t := BrickSwap.elem ρ (Prefix.cut s false) (Prefix.cut s true) hd
  have ht : t ≠ 1 := by
    intro h
    let x : Box S := fun _ _ => false
    have he := congrArg (fun g : localGroup ρ => g.val ((Prefix.cut s false).chart x)) h
    change t.val ((Prefix.cut s false).chart x) = (Prefix.cut s false).chart x at he
    rw [show t.val ((Prefix.cut s false).chart x)=(Prefix.cut s true).chart x from
      BrickSwap.elem_left ρ _ _ hd x] at he
    exact Set.disjoint_left.mp hd (Prefix.chart_mem_brick _ x) (he ▸ Prefix.chart_mem_brick _ x)
  exact ⟨⟨t,1,ht⟩⟩

theorem localGroup_simple [Infinite S] : IsSimpleGroup (localGroup ρ) := by
  apply (isSimpleGroup_iff _).mpr
  refine ⟨localGroup_nontrivial ρ,?_⟩
  intro N hN
  let := hN
  by_cases hn : N=⊥
  · exact Or.inl hn
  right
  have he : ∃ f : localGroup ρ, f ∈ N ∧ f ≠ 1 := by
    by_contra hh
    push Not at hh
    apply hn
    apply le_antisymm
    · intro g hg
      exact Subgroup.mem_bot.mpr (hh g hg)
    · exact bot_le
  obtain ⟨f,hf,hf1⟩ := he
  apply top_unique
  intro g _
  apply (QuotientGroup.eq_one_iff g).mp
  exact SimplicityProducer.hom_eq_one_of_nontrivial_kernel ρ (QuotientGroup.mk' N)
    hf1 ((QuotientGroup.eq_one_iff f).mpr hf) g
end TwistedBrin

end
end

section

noncomputable section

end
end

end OAI
