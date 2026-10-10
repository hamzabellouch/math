import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalSeriesEvaluation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)

noncomputable def globalTensorComponent (k l : SlopeWeight c η hc θ) :
    UnitalShuffle a c η hc θ ⊗[ℚ] UnitalShuffle a c η hc θ →ₗ[ℚ]
      unitalComponent a c η hc θ k ⊗[ℚ] unitalComponent a c η hc θ l :=
  TensorProduct.map (DirectSum.component ℚ _ (unitalComponent a c η hc θ) k)
    (DirectSum.component ℚ _ (unitalComponent a c η hc θ) l)

lemma globalComponent_lof_ne (k l : SlopeWeight c η hc θ) (h : l≠k)
    (x : unitalComponent a c η hc θ l) :
    DirectSum.component ℚ _ (unitalComponent a c η hc θ) k
      (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) l x)=0 := by
  rw [DirectSum.component.of, dite_eq_right h]

lemma unitalSourceTensorGradeEquiv_symm_part (d e : I → ℕ) (W v : ℤ)
    (x : UnitalSourceGrade a c η hc θ d v) (y : UnitalSourceGrade a c η hc θ e (W-v)) :
    (unitalSourceTensorGradeEquiv a c η hc θ d e W).symm
      (unitalTensorGradeInclusionW a c η hc θ d e W v (x⊗ₜ[ℚ]y))=
      DirectSum.lof ℚ ℤ (fun v=>UnitalSourceGrade a c η hc θ d v⊗[ℚ]UnitalSourceGrade a c η hc θ e (W-v)) v (x⊗ₜ[ℚ]y) :=
  tensorGradeEquiv_symm_inclusion _ _ _ _ W v _

lemma globalTensorComponent_inclusion (d e : slopeDimensions c η hc θ) (W u : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalTensorComponent a c η hc θ (d,u) (e,W-u) (globalTensorGradeInclusion a c η hc θ d e W x)=
      DirectSum.component ℚ ℤ _ u ((unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm x) := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy]
  | ht v x y =>
    rw [globalTensorGradeInclusion_part]
    rw [unitalSourceTensorGradeEquiv_symm_part]
    change TensorProduct.map _ _ (_⊗ₜ[ℚ]_)=_
    rw [TensorProduct.map_tmul]
    by_cases hv : v=u
    · subst v
      simp only [DirectSum.component.lof_self]
    · rw [globalComponent_lof_ne a c η hc θ (d,u) (d,v) (by simpa using hv),TensorProduct.zero_tmul,
        DirectSum.component.of,dite_eq_right hv]

lemma globalTensorGradeInclusion_injective (d e : slopeDimensions c η hc θ) (W : ℤ) :
    Function.Injective (globalTensorGradeInclusion a c η hc θ d e W) := by
  intro x y h
  apply (unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm.injective
  apply DirectSum.ext_component ℚ
  intro u
  simpa only [globalTensorComponent_inclusion] using
    congrArg (globalTensorComponent a c η hc θ (d,u) (e,W-u)) h

lemma globalTensorComponent_inclusion_ne_left (k l : SlopeWeight c η hc θ)
    (d e : slopeDimensions c η hc θ) (h : d≠k.1) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalTensorComponent a c η hc θ k l (globalTensorGradeInclusion a c η hc θ d e W x)=0 := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero]
  | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  | ht u x y =>
    rw [globalTensorGradeInclusion_part]
    change TensorProduct.map _ _ (_⊗ₜ[ℚ]_)=0
    rw [TensorProduct.map_tmul,globalComponent_lof_ne a c η hc θ k (d,u)
      (fun he=>h (congrArg Prod.fst he)),TensorProduct.zero_tmul]

lemma globalTensorComponent_split_ne (k : SlopeWeight c η hc θ)
    (s t : SlopeSplit c η hc θ k.1.val) (h : t≠s) (u : ℤ)
    (x : unitalComponent a c η hc θ k) :
    globalTensorComponent a c η hc θ (⟨left s.val,s.property.1⟩,u)
      (⟨right s.val,s.property.2⟩,k.2-u) (globalSplitCoproduct a c η hc θ k t x)=0 := by
  apply globalTensorComponent_inclusion_ne_left
  intro he
  apply h
  exact Subtype.ext (DimensionSplit.ext (congrArg Subtype.val he))

lemma globalTensorComponent_coproduct (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (u : ℤ) (x : unitalComponent a c η hc θ k) :
    globalTensorComponent a c η hc θ (⟨left s.val,s.property.1⟩,u)
      (⟨right s.val,s.property.2⟩,k.2-u)
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
    globalTensorComponent a c η hc θ (⟨left s.val,s.property.1⟩,u)
      (⟨right s.val,s.property.2⟩,k.2-u) (globalSplitCoproduct a c η hc θ k s x) := by
  rw [globalCoproduct_lof,map_sum,Finset.sum_eq_single s]
  · intro t ht hts
    exact globalTensorComponent_split_ne a c η hc θ k s t hts u x
  · simp

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalComponent_unit (k : SlopeWeight c η hc θ) (hk : k.1.val≠0) :
    DirectSum.component ℚ _ (unitalComponent a c η hc θ) k (globalUnit a c η hc θ)=0 :=
  globalComponent_lof_ne a c η hc θ k (0,0)
    (fun h=>hk (congrArg (fun z : SlopeWeight c η hc θ=>z.1.val) h).symm) _

lemma globalPrimitive_split_zero (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (hl : left s.val≠0) (hr : right s.val≠0)
    (x : unitalComponent a c η hc θ k)
    (hx : DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈globalPrimitives a c η hc θ) :
    globalSplitCoproduct a c η hc θ k s x=0 := by
  change globalTensorGradeInclusion a c η hc θ _ _ _ _=0
  rw [←map_zero (globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ k.2)]
  congr 1
  apply (unitalSourceTensorGradeEquiv a c η hc θ (left s.val) (right s.val) k.2).symm.injective
  apply DirectSum.ext_component ℚ
  intro u
  rw [map_zero,map_zero]
  rw [←globalTensorComponent_inclusion a c η hc θ ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ k.2 u]
  change globalTensorComponent a c η hc θ _ _ (globalSplitCoproduct a c η hc θ k s x)=0
  rw [←globalTensorComponent_coproduct,(mem_globalPrimitives a c η hc θ _).mp hx,map_add]
  change TensorProduct.map _ _ (_⊗ₜ[ℚ]_) + TensorProduct.map _ _ (_⊗ₜ[ℚ]_)=0
  rw [TensorProduct.map_tmul,TensorProduct.map_tmul,globalComponent_unit a c η hc θ (⟨left s.val,s.property.1⟩,u) hl,
    globalComponent_unit a c η hc θ (⟨right s.val,s.property.2⟩,k.2-u) hr,TensorProduct.tmul_zero,TensorProduct.zero_tmul,add_zero]

lemma globalPrimitive_iff_split_zero (k : SlopeWeight c η hc θ) (hk : k.1.val≠0)
    (x : unitalComponent a c η hc θ k) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈globalPrimitives a c η hc θ ↔
      ∀ s : SlopeSplit c η hc θ k.1.val,left s.val≠0 → right s.val≠0 →
        globalSplitCoproduct a c η hc θ k s x=0 := by
  constructor
  · exact fun hx s hl hr=>globalPrimitive_split_zero a c η hc θ k s hl hr x hx
  · intro hx
    rw [mem_globalPrimitives,globalCoproduct_lof]
    let l := slopeSplitZeroLeft c η hc θ k.1
    let r := slopeSplitZeroRight c η hc θ k.1
    have hlr : l≠r := by
      intro h
      have hh := congrArg (fun s : SlopeSplit c η hc θ k.1.val=>left s.val) h
      exact hk hh.symm
    have hs : (∑ s : SlopeSplit c η hc θ k.1.val,globalSplitCoproduct a c η hc θ k s x)=
        ∑ s∈({l,r} : Finset _),globalSplitCoproduct a c η hc θ k s x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ hs
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hs
      exact hx s (slopeSplit_ne_left_zero c η hc θ k.1 s hs.1)
        (slopeSplit_ne_right_zero c η hc θ k.1 s hs.2)
    rw [hs,Finset.sum_pair hlr,globalSplitCoproduct_zero_left,globalSplitCoproduct_zero_right,add_comm]

end ElementaryPositivity.RawShuffle

end

end OAI
