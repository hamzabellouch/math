import OAI.Geometry.Convex.GeneralMahler.Brouwer.Scarf

namespace OAI
/-! Add labeled slack/ghost vertices. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] [Nonempty T]
structure GOrders (I T : Type*) extends Orders I (I⊕T) where
  low : ∀ i x, rank i (.inl i) < rank i (.inr x)
  high : ∀ i j, i≠j → ∀ x, rank i (.inr x) < rank i (.inl j)

variable (q : GOrders I T)
def inside (s:Finset (I⊕T)) := ∃ x, Sum.inr x ∈ s

-- Either one or two extensions
omit [Nonempty T] in
lemma extensions_two {d: Finset (I⊕T)} (hd : door q.toOrders d) (hu : inside d) :
    ∃ s₁ s₂, s₁ ≠ s₂ ∧ ∀ s, room q.toOrders s ∧ d⊆s ↔ s=s₁ ∨ s=s₂ := by
  obtain ⟨x,hx⟩ := hu
  let r := q.toOrders
  obtain ⟨v,hv⟩ := min_nodes r (show d.Nonempty from ⟨_,hx⟩)
  have he := min_cover r hd.2 hv
  have hg (i j:I) (hi:i≠j) : v i ≠ Sum.inl j := by
    intro h
    have H := (hv i).2 (.inr x) hx
    rw [h] at H
    exact not_lt_of_ge H (q.high i j hi x)
  have hm : (univ:Finset I).card=(univ.image v).card+1 := by rw [card_univ,he]; exact hd.1
  obtain ⟨a,-,b,-,ha,hb,h⟩ := duplicate_pair v hm
  have hh (i j:I) (hi:i≠j) (hj:v i=v j) : (cand r v i).Nonempty := by
    refine ⟨Sum.inl i, (mem_cand' r).mpr ?_⟩
    intro l hl
    cases e:v l with
    | inl y =>
      have hy : l=y := by
        by_contra hn
        exact hg l y hn e
      subst l; exact (q.low y x).trans (q.high y _ hl _)
    | inr t => exact q.high _ _ hl _
  obtain ⟨s,hs,Hs⟩ := Finset.exists_max_image (cand r v a) (r.rank a) (hh _ _ ha hb)
  obtain ⟨t,ht,Ht⟩ := Finset.exists_max_image (cand r v b) (r.rank b) (hh _ _ (Ne.symm ha) hb.symm)
  have H₁ : s∉d ∧ room r (insert s d) :=
    (extension_spec r hd hv).mpr ⟨a,⟨b,ha,hb⟩,hs,Hs⟩
  have H₂ : t∉d ∧ room r (insert t d) :=
    (extension_spec r hd hv).mpr ⟨b,⟨a,Ne.symm ha,hb.symm⟩,ht,Ht⟩
  have hst : s ≠ t := by
    rintro rfl
    obtain ⟨i,hi⟩ := hd.2 s
    have he := hi (v i) (hv i).1
    by_cases h:i=a
    · subst i; exact not_lt_of_ge he ((mem_cand' r).mp ht a ha)
    · exact not_lt_of_ge he ((mem_cand' r).mp hs i h)
  refine ⟨insert s d, insert t d,fun ep => ?_,fun y => ?_⟩
  · have hh : s ∈ insert t d := ep ▸ mem_insert_self ..
    exact (mem_insert.mp hh).elim hst H₁.1
  constructor
  · rintro ⟨hr,hdy⟩
    obtain ⟨l,hl,rfl⟩ := Finset.exists_eq_insert_iff.mpr (show d⊆y ∧ d.card+1=y.card from
      ⟨hdy,hd.1.symm.trans hr.1.symm⟩)
    obtain ⟨i,⟨j,hij,heij⟩,hli,Hli⟩ := (extension_spec r hd hv).mp ⟨hl,hr⟩
    rcases h i (mem_univ _) j (mem_univ _) hij heij with ⟨hh,-⟩ | ⟨hh,-⟩
    · subst i
      exact Or.inl (congrArg (fun x => insert x d) (r.inj _ (le_antisymm (Hs _ hli) (Hli _ hs))))
    · subst i
      exact Or.inr (congrArg (fun x => insert x d) (r.inj _ (le_antisymm (Ht _ hli) (Hli _ ht))))
  · rintro (rfl|rfl)
    · exact ⟨H₁.2, subset_insert ..⟩
    · exact ⟨H₂.2, subset_insert ..⟩

def outer (i:I) : Finset (I⊕T) := (univ.erase i).image Sum.inl

omit [Fintype T] [Nonempty T] in
@[simp] lemma mem_outer (i j:I) :
    Sum.inl j ∈ outer (T := T) i ↔ j≠i := by simp [outer]
omit [Fintype T] [Nonempty T] in
@[simp] lemma not_mem_outer (i:I) (x:T) :
    Sum.inr x ∉ outer i := by simp [outer]

-- handles also I singleton
omit [Fintype T] in
lemma outer_door (i:I) : door q.toOrders (outer i) := by
  constructor
  · have h : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
    unfold outer; rw [card_image_of_injective _ Sum.inl_injective,card_erase_of_mem (mem_univ _),card_univ]
    omega
  · intro w
    cases w with
    | inr x =>
      refine ⟨i,fun y hy=>?_⟩
      cases y with
      | inl j =>
        exact (q.high i j (Ne.symm ((mem_outer i j).mp hy)) x).le
      | inr y => exact False.elim (not_mem_outer i y hy)
    | inl j =>
      refine ⟨j,fun y hy=>?_⟩
      cases y with
      | inl y =>
        by_cases he:y=j
        · subst j; exact le_refl _
        · obtain ⟨x⟩ := ‹Nonempty T›
          exact ((q.low j x).trans (q.high j y (Ne.symm he) x)).le
      | inr x => exact (q.low j x).le

lemma extension_outer (i:I) :
    ∃! s, room q.toOrders s ∧ outer i ⊆ s := by
  let r := q.toOrders
  obtain ⟨x,hx,Hx⟩ := Finset.exists_max_image (univ:Finset T) (fun x=>r.rank i (Sum.inr x))
    univ_nonempty
  have hc := (outer_door q i).1
  let s := insert (Sum.inr x) (outer i : Finset (I⊕T))
  refine ⟨s,⟨⟨?_,?_⟩, subset_insert ..⟩,?_⟩
  · change (insert (Sum.inr x) (outer i)).card=_
    rw [card_insert_of_notMem (not_mem_outer i x)]
    exact hc.symm
  · intro y
    cases y with
    | inl j =>
      obtain ⟨j',hj⟩ := (outer_door q i).2 (Sum.inl j)
      refine ⟨j,fun w hw => ?_⟩
      cases w with
      | inr t => exact (q.low j t).le
      | inl k =>
        by_cases he:j=k
        · rw [he]
        · exact ((q.low j x).trans (q.high j k he x)).le
    | inr z =>
      refine ⟨i,fun w hw => ?_⟩
      rcases mem_insert.mp hw with he|he
      · subst w; exact Hx z (mem_univ _)
      cases w with
      | inl j => exact (q.high i j (Ne.symm ((mem_outer i j).mp he)) z).le
      | inr j => exact False.elim (not_mem_outer i j he)
  · rintro z ⟨hz,hzr⟩
    obtain ⟨w,hw,rfl⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨hzr,hc.symm.trans hz.1.symm⟩
    obtain ⟨j,hj⟩ := hz.2 (Sum.inr x)
    have he : j=i := by
      by_contra H
      have ha := hj (Sum.inl j) (mem_insert_of_mem ((mem_outer i j).mpr H))
      exact not_lt_of_ge ha (q.low j x)
    subst j
    cases w with
    | inr y =>
      have hxy : Sum.inr x = Sum.inr y :=
        q.inj i (le_antisymm (hj _ (mem_insert_self ..)) (Hx y (mem_univ _)))
      rw [← hxy]
    | inl j =>
      have hji : j=i := by
        by_contra he
        exact hw ((mem_outer i j).mpr he)
      subst j
      exact False.elim (not_lt_of_ge (hj _ (mem_insert_self ..)) (q.low i x))
end GeneralMahler.Scarf

end

end OAI
