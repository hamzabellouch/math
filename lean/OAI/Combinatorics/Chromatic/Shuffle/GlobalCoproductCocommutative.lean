import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalTensorGradeProduct

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma unitalGradeCast_trans (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e f : I → ℕ} {U V W : ℤ}
    (hde : d=e) (hef : e=f) (hUV : U=V) (hVW : V=W)
    (x : UnitalSourceGrade a c η hc θ d U) :
    unitalGradeCast a c η hc θ hef hVW (unitalGradeCast a c η hc θ hde hUV x)=
      unitalGradeCast a c η hc θ (hde.trans hef) (hUV.trans hVW) x := by
  subst e; subst f; subst V; subst W
  rfl

namespace DimensionSplit

def swap {d : I → ℕ} (s : DimensionSplit d) : DimensionSplit d :=
  ofPair (right s) (left s) ((add_comm _ _).trans (left_add_right s))
omit [Fintype I] [DecidableEq I] in
@[simp] lemma left_swap {d : I → ℕ} (s : DimensionSplit d) : left (swap s)=right s :=
  left_ofPair _ _ _
omit [Fintype I] [DecidableEq I] in
@[simp] lemma right_swap {d : I → ℕ} (s : DimensionSplit d) : right (swap s)=left s :=
  right_ofPair _ _ _
omit [Fintype I] [DecidableEq I] in
@[simp] lemma swap_swap {d : I → ℕ} (s : DimensionSplit d) : swap (swap s)=s := by
  apply DimensionSplit.ext
  simp only [left_swap,right_swap]
end DimensionSplit

noncomputable def slopeSplitSwap (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :
    SlopeSplit c η hc θ d ≃ SlopeSplit c η hc θ d where
  toFun s:=⟨DimensionSplit.swap s.val,by simpa only [left_swap,right_swap] using s.property.symm⟩
  invFun s:=⟨DimensionSplit.swap s.val,by simpa only [left_swap,right_swap] using s.property.symm⟩
  left_inv s:=by apply Subtype.ext; exact swap_swap s.val
  right_inv s:=by apply Subtype.ext; exact swap_swap s.val

noncomputable def globalSignedComm (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) :
    UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  (TensorProduct.comm ℚ _ _).toLinearMap.comp (globalSignOperator a c η hc θ)

lemma globalSignOperator_inclusion (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    globalSignOperator a c η hc θ (globalTensorGradeInclusion a c η hc θ d e W x)=
      (-1:ℚ)^eulerForm a d.val e.val • globalTensorGradeInclusion a c η hc θ d e W x := by
  induction x using unitalTensorGrade_induction a c η hc θ d.val e.val W with
  | hz => simp only [map_zero,smul_zero]
  | ha x y hx hy => simp only [map_add,smul_add,hx,hy]
  | ht u x y => rw [globalTensorGradeInclusion_part,globalSignOperator_tmul_lof]

lemma globalPairCoproduct_swap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d e : slopeDimensions c η hc θ) {t : I → ℕ} (h : d.val+e.val=t)
    (W : ℤ) (x : UnitalSourceGrade a c η hc θ t W) :
    globalTensorGradeInclusion a c η hc θ e d W
      (unitalGradeCoproduct a c η hc θ e.val d.val (e.property.compatible d.property) W
        (unitalGradeCast a c η hc θ ((add_comm _ _).trans h).symm rfl x))=
      globalSignedComm a c η hc θ
        (globalTensorGradeInclusion a c η hc θ d e W
          (unitalGradeCoproduct a c η hc θ d.val e.val (d.property.compatible e.property) W
            (unitalGradeCast a c η hc θ h.symm rfl x))) := by
  have hC := unitalGradeCoproduct_cocommutative a c η hc θ hχ d.val e.val
    d.property e.property W (unitalGradeCast a c η hc θ h.symm rfl x)
  rw [unitalGradeCast_trans] at hC
  rw [hC,map_smul,globalTensorGradeInclusion_comm]
  rw [globalSignedComm,LinearMap.comp_apply,globalSignOperator_inclusion,map_smul]
  rfl

lemma globalSplitCoproduct_dimensions (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (d e : I → ℕ)
    (hd : left s.val=d) (he : right s.val=e)
    (hds : OnSlopeOrZero c η θ d) (hes : OnSlopeOrZero c η θ e)
    (h : d+e=k.1.val) (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k s x=
      globalTensorGradeInclusion a c η hc θ ⟨d,hds⟩ ⟨e,hes⟩ k.2
        (unitalGradeCoproduct a c η hc θ d e (hds.compatible hes) k.2
          (unitalGradeCast a c η hc θ h.symm rfl x)) := by
  subst d; subst e
  rfl

lemma globalSplitCoproduct_swap (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (k : SlopeWeight c η hc θ) (s : SlopeSplit c η hc θ k.1.val)
    (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k (slopeSplitSwap c η hc θ k.1.val s) x=
      globalSignedComm a c η hc θ (globalSplitCoproduct a c η hc θ k s x) := by
  rw [globalSplitCoproduct_dimensions a c η hc θ k
    (slopeSplitSwap c η hc θ k.1.val s) (right s.val) (left s.val)
    (left_swap s.val) (right_swap s.val) s.property.2 s.property.1
    ((add_comm _ _).trans (left_add_right s.val)) x]
  rw [globalSplitCoproduct_dimensions a c η hc θ k s (left s.val) (right s.val)
    rfl rfl s.property.1 s.property.2 (left_add_right s.val) x]
  exact globalPairCoproduct_swap a c η hc θ hχ
    ⟨left s.val,s.property.1⟩ ⟨right s.val,s.property.2⟩ (left_add_right s.val) k.2 x

theorem globalCoproduct_cocommutative (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (x : UnitalShuffle a c η hc θ) :
    globalSignedComm a c η hc θ (globalCoproduct a c η hc θ x)=
      globalCoproduct a c η hc θ x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of k x =>
    change globalSignedComm a c η hc θ
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
        globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)
    rw [globalCoproduct_lof]
    simp only [map_sum]
    calc
      _=∑ s : SlopeSplit c η hc θ k.1.val,
        globalSplitCoproduct a c η hc θ k (slopeSplitSwap c η hc θ k.1.val s) x :=
          Finset.sum_congr rfl (fun s _=>(globalSplitCoproduct_swap a c η hc θ hχ k s x).symm)
      _=_ := Equiv.sum_comp (slopeSplitSwap c η hc θ k.1.val)
        (fun s : SlopeSplit c η hc θ k.1.val => globalSplitCoproduct a c η hc θ k s x)
end ElementaryPositivity.RawShuffle

end

end OAI
