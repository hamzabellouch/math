import Mathlib
import OAI.Geometry.HyperbolicGroups.LeafMargin

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

abbrev ExtPos (support : R → Finset F) (U : Finset F) (j₀ : B) :=
  {j : B // j ≠ j₀} × {r : R // ¬support r ⊆ U}

def extPos (support : R → Finset F) (U : Finset F) (j₀ : B)
    (s : ExtPos support U j₀) : Pos (B := B) support U := .inr (s.1.val,s.2)

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq F] [DecidableEq R]
  [DecidableEq B] [Nonempty B] in
lemma extPos_injective (support : R → Finset F) (U : Finset F) (j₀ : B) :
    Function.Injective (extPos support U j₀) := by
  intro s t h
  have hh := Sum.inr.inj h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun q : B × {r : R // ¬support r ⊆ U} => q.2) hh)

/-- All fields belonging to the specified branch are fixed in an extension. -/
def branchPins (U : Finset F) (j₀ : B) : Finset (Var (B := B) U) :=
  Finset.univ.image (coord U j₀)

omit [Fintype B] [Nonempty B] in
@[simp] lemma mem_branchPins_inl (U : Finset F) (j₀ : B) (f : U) :
    Sum.inl f ∈ branchPins U j₀ := by
  exact Finset.mem_image.mpr ⟨f.val,Finset.mem_univ _,coord_in U j₀ f⟩

omit [Fintype B] [Nonempty B] in
@[simp] lemma mem_branchPins_inr (U : Finset F) (j₀ j : B) (f : {f : F // f ∉ U}) :
    Sum.inr (j,f) ∈ branchPins U j₀ ↔ j = j₀ := by
  constructor
  · intro h
    obtain ⟨g,_,hg⟩ := Finset.mem_image.mp h
    exact (coord_eq_inr U hg).1.symm
  · intro h
    subst j
    exact Finset.mem_image.mpr ⟨f.val,Finset.mem_univ _,coord_out U j₀ f⟩

omit [Nonempty B] in
lemma extension_free_card (U : Finset F) (j₀ : B) (W : Finset (Var (B := B) U)) :
    (W \ branchPins U j₀).card = ∑ j : {j : B // j ≠ j₀}, (wing U W j.val).card := by
  let e : {j : B // j ≠ j₀} × {f : F // f ∉ U} → Var (B := B) U :=
    fun jf => .inr (jf.1.val,jf.2)
  have hi : Function.Injective e := by
    intro a b h
    have hh := Sum.inr.inj h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun q : B × {f : F // f ∉ U} => q.2) hh)
  let T : Finset ({j : B // j ≠ j₀} × {f : F // f ∉ U}) :=
    Finset.univ.filter (fun jf => e jf ∈ W)
  have he : W \ branchPins U j₀ = T.image e := by
    ext v
    cases v with
    | inl f => simp [T,e]
    | inr jf =>
      obtain ⟨j,f⟩ := jf
      simp only [Finset.mem_sdiff,mem_branchPins_inr,Finset.mem_image]
      constructor
      · rintro ⟨hm,hj⟩
        exact ⟨(⟨j,hj⟩,f),by simpa [T,e] using hm,rfl⟩
      · rintro ⟨⟨k,g⟩,hkg,hh⟩
        have hx : (k.val,g) = (j,f) := Sum.inr.inj hh
        obtain rfl : k.val = j := congrArg Prod.fst hx
        obtain rfl : g = f := congrArg Prod.snd hx
        exact ⟨by simpa [T,e] using hkg,k.property⟩
  rw [he,Finset.card_image_of_injective _ hi]
  have hcard := Finset.sum_card_fiberwise_eq_card_filter (s := T)
    (t := (Finset.univ : Finset {j : B // j ≠ j₀})) (g := Prod.fst)
  simp only [Finset.mem_univ,Finset.filter_true] at hcard
  rw [← hcard]
  apply Finset.sum_congr rfl
  intro j _
  let g : {f : F // f ∉ U} → {j : B // j ≠ j₀} × {f : F // f ∉ U} := fun f => (j,f)
  have hg : Function.Injective g := fun _ _ h => congrArg Prod.snd h
  have hf : T.filter (fun q => q.1 = j) = (Finset.univ.filter (fun f => f.val ∈ wing U W j.val)).image g := by
    ext q
    obtain ⟨k,f⟩ := q
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,T,e]
    simp only [g,Prod.mk.injEq]
    constructor
    · rintro ⟨hm,hkj⟩
      subst k
      exact ⟨f,(mem_wing U W j.val f).mpr hm,rfl,rfl⟩
    · rintro ⟨f',hm,rfl,rfl⟩
      exact ⟨(mem_wing U W j.val f').mp hm,rfl⟩
  rw [hf,Finset.card_image_of_injective _ hg]
  have hj : wing U W j.val = (Finset.univ.filter (fun f : {f : F // f ∉ U} => f.val ∈ wing U W j.val)).image Subtype.val := by
    ext f
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hf
      exact ⟨⟨f,fun h => Finset.disjoint_left.mp (wing_disjoint U W j.val) h hf⟩,hf,rfl⟩
    · rintro ⟨g,hg,rfl⟩
      exact hg
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm.trans (congrArg Finset.card hj.symm)

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq R] in
lemma extension_active (support : R → Finset F) (U : Finset F) (j₀ : B)
    (J : Finset (ExtPos support U j₀)) (hJ : J.Nonempty) :
    ∃ j : {j : B // j ≠ j₀}, (wing U (J.biUnion (fun s => rowSupport support U (extPos support U j₀ s))) j.val).Nonempty := by
  obtain ⟨⟨j,r⟩,hjr⟩ := hJ
  have hr : ∃ f ∈ support r.val, f ∉ U := by simpa [Finset.subset_iff] using r.property
  obtain ⟨f,hf,hfu⟩ := hr
  refine ⟨j,f,(mem_wing U _ j.val ⟨f,hfu⟩).mpr ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(j,r),hjr,?_⟩
  exact Finset.mem_image.mpr ⟨f,hf,coord_out U j.val ⟨f,hfu⟩⟩

omit [DecidableEq R] in
lemma extension_selected_cost (P : SparsePattern.Pattern F R) (U : Finset F) (j₀ : B)
    (J : Finset (ExtPos P.support U j₀)) :
    let W := J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))
    (∑ s ∈ J, P.cost s.2.val) ≤ ∑ j : {j : B // j ≠ j₀}, P.branchCost U U (wing U W j.val) := by
  dsimp only
  let W := J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))
  have hh : ∀ s ∈ J, P.support s.2.val ⊆ U ∪ wing U W s.1.val := by
    intro s hs
    have he := (support_subset P.support U W (extPos P.support U j₀ s)).mp
      (show rowSupport P.support U (extPos P.support U j₀ s) ⊆ W from Finset.subset_biUnion_of_mem (fun t : ExtPos P.support U j₀ => rowSupport P.support U (extPos P.support U j₀ t)) hs)
    exact he.trans (Finset.union_subset_union_left (center_subset U W))
  calc
    _ = ∑ s ∈ J, if P.support s.2.val ⊆ U ∪ wing U W s.1.val then P.cost s.2.val else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [ite_eq_left (hh s hs)]
    _ ≤ ∑ s : ExtPos P.support U j₀, if P.support s.2.val ⊆ U ∪ wing U W s.1.val then P.cost s.2.val else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro s _ _; split_ifs; exact P.nonneg _; rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_subtype_ite (fun r => ¬P.support r ⊆ U)
        (fun r => if P.support r ⊆ U ∪ wing U W j.val then P.cost r else 0)]
      change _ = P.branchCost U U (wing U W j.val)
      unfold SparsePattern.Pattern.branchCost
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : P.support r ⊆ U <;> by_cases h' : P.support r ⊆ U ∪ wing U W j.val <;> simp [h,h']

omit [DecidableEq R] in
lemma extension_critical_gap (P : SparsePattern.Pattern F R) (U : Finset F) (j₀ : B)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U)
    (J : Finset (ExtPos P.support U j₀)) (hJ : J.Nonempty) :
    1 ≤ (((J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))) \ branchPins U j₀).card : ℤ) -
      ∑ s ∈ J, P.cost s.2.val := by
  let W := J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))
  have hm := P.extension_margin (fun j : {j : B // j ≠ j₀} => wing_disjoint U W j.val)
    (extension_active P.support U j₀ J hJ) gap
  have hs := extension_selected_cost P U j₀ J
  rw [extension_free_card]
  push_cast
  simp only [Finset.sum_sub_distrib] at hm
  change 1 ≤ (∑ x : {j : B // j ≠ j₀}, ((wing U W x.val).card : ℤ)) - ∑ s ∈ J, P.cost s.2.val
  change (∑ s ∈ J, P.cost s.2.val) ≤ ∑ j : {j : B // j ≠ j₀}, P.branchCost U U (wing U W j.val) at hs
  omega

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
