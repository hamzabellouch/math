import Mathlib
import OAI.Geometry.HyperbolicGroups.StarBudget
import OAI.Geometry.HyperbolicGroups.StarModel

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [DecidableEq F] [DecidableEq B]

def center (U : Finset F) (W : Finset (Var (B := B) U)) : Finset F :=
  W.toLeft.image Subtype.val

def wing (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) : Finset F :=
  (W.toRight.filter (fun jf => jf.1 = j)).image (fun jf => jf.2.val)

omit [DecidableEq B] in
lemma center_subset (U : Finset F) (W : Finset (Var (B := B) U)) : center U W ⊆ U := by
  intro f hf
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hf
  exact v.property

lemma wing_disjoint (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) :
    Disjoint U (wing U W j) := by
  apply Finset.disjoint_left.mpr
  intro f hf hg
  obtain ⟨⟨k,g⟩,_,hgf⟩ := Finset.mem_image.mp hg
  exact g.property (hgf ▸ hf)

omit [DecidableEq B] in
lemma mem_center (U : Finset F) (W : Finset (Var (B := B) U)) (f : U) :
    f.val ∈ center U W ↔ Sum.inl f ∈ W := by
  simp only [center, Finset.mem_image,Finset.mem_toLeft]
  constructor
  · rintro ⟨g,hg,he⟩
    simpa only [Subtype.ext he] using hg
  · exact fun h => ⟨f,h,rfl⟩

lemma mem_wing (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) (f : {f : F // f ∉ U}) :
    f.val ∈ wing U W j ↔ Sum.inr (j,f) ∈ W := by
  simp only [wing,Finset.mem_image,Finset.mem_filter,Finset.mem_toRight]
  constructor
  · rintro ⟨⟨k,g⟩,⟨hg,hkj⟩,hgf⟩
    dsimp only at hkj hgf
    subst k
    simpa only [Subtype.ext hgf] using hg
  · exact fun h => ⟨(j,f),⟨h,rfl⟩,rfl⟩

lemma coord_mem (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) (f : F) :
    coord U j f ∈ W ↔ f ∈ center U W ∪ wing U W j := by
  by_cases hf : f ∈ U
  · have hn : f ∉ wing U W j := fun h => Finset.disjoint_left.mp (wing_disjoint U W j) hf h
    simp only [coord,hf,↓reduceDIte,Finset.mem_union,hn,or_false]
    exact (mem_center U W ⟨f,hf⟩).symm
  · have hn : f ∉ center U W := fun h => hf (center_subset U W h)
    simp only [coord,hf,↓reduceDIte,Finset.mem_union,hn,false_or]
    exact (mem_wing U W j ⟨f,hf⟩).symm

omit [DecidableEq B] in
lemma card_center (U : Finset F) (W : Finset (Var (B := B) U)) :
    (center U W).card = W.toLeft.card := Finset.card_image_of_injective _ Subtype.val_injective

lemma card_wing (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) :
    (wing U W j).card = (W.toRight.filter fun jf => jf.1 = j).card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  apply Prod.ext
  · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  · exact Subtype.ext he

lemma card_decomposition [Fintype B] (U : Finset F) (W : Finset (Var (B := B) U)) :
    W.card = (center U W).card + ∑ j, (wing U W j).card := by
  rw [card_center]
  simp_rw [card_wing]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp only [Finset.mem_univ,Finset.filter_true]
  exact Finset.card_toLeft_add_card_toRight.symm

variable [Nonempty B]

lemma support_subset (support : R → Finset F) (U : Finset F)
    (W : Finset (Var (B := B) U)) (s : Pos (B := B) support U) :
    rowSupport support U s ⊆ W ↔
      support (array support U s) ⊆ center U W ∪ wing U W (branch support U s) := by
  rw [rowSupport,Finset.image_subset_iff]
  simp only [coord_mem]
  rfl

lemma center_support_subset (support : R → Finset F) (U : Finset F)
    (W : Finset (Var (B := B) U)) (r : {r : R // support r ⊆ U}) :
    rowSupport support U (Sum.inl r) ⊆ W ↔ support r.val ⊆ center U W := by
  rw [support_subset]
  constructor
  · intro h f hf
    rcases Finset.mem_union.mp (h hf) with hh | hh
    · exact hh
    · exact False.elim (Finset.disjoint_left.mp (wing_disjoint U W _) (r.property hf) hh)
  · exact fun h => h.trans Finset.subset_union_left

/-- A finite sum over an explicitly selected subtype, allowing the row array
cost to be expressed without introducing independent branch arrays. -/
lemma sum_subtype_ite {T : Type*} [Fintype T] (p : T → Prop) [DecidablePred p]
    (f : T → ℤ) : (∑ x : {x : T // p x}, f x.val) = ∑ x, if p x then f x else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro x; simp) f,
    Finset.sum_filter]

variable [Fintype F] [Fintype R] [Fintype B]

lemma saturated_cost (P : SparsePattern.Pattern F R) (U : Finset F)
    (W : Finset (Var (B := B) U)) :
    (∑ s : Pos (B := B) P.support U,
      if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0) =
      (∑ r, if P.support r ⊆ center U W then P.cost r else 0) +
      ∑ j, P.branchCost U (center U W) (wing U W j) := by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  congr 1
  · simp_rw [center_support_subset]
    change (∑ r : {r : R // P.support r ⊆ U}, if P.support r.val ⊆ center U W then P.cost r.val else 0) = _
    rw [sum_subtype_ite (fun r => P.support r ⊆ U)
      (fun r => if P.support r ⊆ center U W then P.cost r else 0)]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : P.support r ⊆ center U W
    · simp [h,h.trans (center_subset U W)]
    · simp [h]
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [support_subset]
    change (∑ r : {r : R // ¬P.support r ⊆ U},
      if P.support r.val ⊆ center U W ∪ wing U W j then P.cost r.val else 0) = _
    rw [sum_subtype_ite (fun r => ¬P.support r ⊆ U)
      (fun r => if P.support r ⊆ center U W ∪ wing U W j then P.cost r else 0)]
    unfold SparsePattern.Pattern.branchCost
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : P.support r ⊆ U <;>
      by_cases h' : P.support r ⊆ center U W ∪ wing U W j <;> simp [h,h']

lemma star_exponent_eq (P : SparsePattern.Pattern F R) (U : Finset F)
    (W : Finset (Var (B := B) U)) :
    P.starExponent U (center U W) (wing U W) = (W.card : ℤ) -
      ∑ s : Pos (B := B) P.support U,
        if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0 := by
  rw [saturated_cost,card_decomposition]
  simp only [Nat.cast_add,Nat.cast_sum,SparsePattern.Pattern.starExponent,
    SparsePattern.Pattern.exponent,Finset.sum_sub_distrib]
  ring

lemma selected_cost (P : SparsePattern.Pattern F R) (U : Finset F)
    (J : Finset (Pos (B := B) P.support U))
    (W : Finset (Var (B := B) U)) (hW : ∀ s ∈ J, rowSupport P.support U s ⊆ W) :
    (∑ s ∈ J, P.cost (array P.support U s)) ≤
      ∑ s : Pos (B := B) P.support U,
        if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0 := by
  calc
    _ = ∑ s ∈ J, if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [hW s hs,↓reduceIte]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun s _ _ => by split_ifs; exact P.nonneg _; rfl)

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
