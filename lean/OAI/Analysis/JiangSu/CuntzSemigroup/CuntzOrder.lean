import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixSums
import OAI.Analysis.JiangSu.TraceCone.MatrixBlockNorm

namespace OAI


namespace Pureness
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace PositiveCuntzClass

def mk (a : {a : A // 0 ≤ a}) : PositiveCuntzClass A := Quotient.mk _ a

instance : LE (PositiveCuntzClass A) where
  le x y := Quotient.liftOn₂ x y (fun a b => CuntzSubequiv a.val b.val) (by
    intro a b c d hac hbd
    apply propext
    exact ⟨fun h => hac.2.trans (h.trans hbd.1),
      fun h => hac.1.trans (h.trans hbd.2)⟩)

@[simp] theorem mk_le_mk (a b : {a : A // 0 ≤ a}) :
    mk a ≤ mk b ↔ CuntzSubequiv a.val b.val := Iff.rfl

instance partialOrder : PartialOrder (PositiveCuntzClass A) where
  le_refl x := by
    induction x using Quotient.inductionOn with
    | h a => exact cstar_cuntzSubequiv_refl a.val
  le_trans x y z := by
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        induction z using Quotient.inductionOn with
        | h c => exact fun hab hbc => CuntzSubequiv.trans hab hbc
  le_antisymm x y := by
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b => exact fun hab hba => Quotient.sound ⟨hab, hba⟩

instance : Bot (PositiveCuntzClass A) := ⟨mk ⟨0, le_rfl⟩⟩

instance orderBot : OrderBot (PositiveCuntzClass A) where
  bot_le x := by
    induction x using Quotient.inductionOn with
    | h a => exact zero_cuntzSubequiv a.val

@[simp] theorem mk_eq_bot_iff (a : {a : A // 0 ≤ a}) :
    mk a = ⊥ ↔ a.val = 0 := by
  change Quotient.mk _ a = Quotient.mk _ ⟨0, le_rfl⟩ ↔ a.val = 0
  rw [Quotient.eq]
  change (CuntzSubequiv a.val 0 ∧ CuntzSubequiv 0 a.val) ↔ a.val = 0
  simp only [cuntzSubequiv_zero_iff, zero_cuntzSubequiv, and_true]

end PositiveCuntzClass
end Pureness


open scoped CStarAlgebra

noncomputable section
namespace Pureness
open TraceCone

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cuntzSubequiv_iff_shared {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (a b : Positive D) :
    CuntzSubequiv a.1 b.1 ↔ TraceCone.CuntzBelow a b := by
  rw [cuntzSubequiv_iff_norm]
  simp only [TraceCone.CuntzBelow, norm_sub_rev]

def completedSharedClass (a : Positive (CornerCompletion A)) :
    TraceCone.CuntzClass (TraceCone.MatrixLimit A) :=
  TraceCone.CuntzClass.mk (Positive.map sharedMatrixEquiv.symm.toNonUnitalStarAlgHom a)

lemma shared_positive_roundtrip (a : Positive (CornerCompletion A)) :
    Positive.map sharedMatrixEquiv.toNonUnitalStarAlgHom
      (Positive.map sharedMatrixEquiv.symm.toNonUnitalStarAlgHom a) = a := by
  apply Subtype.ext
  exact sharedMatrixEquiv.apply_symm_apply a.1

lemma shared_cuntz_map_equiv {D E : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] [NonUnitalCStarAlgebra E]
    [PartialOrder E] [StarOrderedRing E] (e : D ≃⋆ₐ[ℂ] E) (a b : Positive D) :
    TraceCone.CuntzBelow (Positive.map e.toNonUnitalStarAlgHom a)
      (Positive.map e.toNonUnitalStarAlgHom b) ↔ TraceCone.CuntzBelow a b := by
  constructor
  · intro h
    have hm := h.map e.symm.toNonUnitalStarAlgHom
    have ha : Positive.map e.symm.toNonUnitalStarAlgHom (Positive.map e.toNonUnitalStarAlgHom a) = a :=
      Subtype.ext (e.symm_apply_apply a.1)
    have hb : Positive.map e.symm.toNonUnitalStarAlgHom (Positive.map e.toNonUnitalStarAlgHom b) = b :=
      Subtype.ext (e.symm_apply_apply b.1)
    rwa [ha,hb] at hm
  · exact fun h => h.map e.toNonUnitalStarAlgHom

theorem completedSharedClass_le_iff (a b : Positive (CornerCompletion A)) :
    completedSharedClass a ≤ completedSharedClass b ↔ CuntzSubequiv a.1 b.1 := by
  unfold completedSharedClass
  rw [TraceCone.CuntzClass.mk_le_mk, shared_cuntz_map_equiv, cuntzSubequiv_iff_shared]

theorem completedSharedClass_surjective : Function.Surjective (completedSharedClass (A := A)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h a =>
    refine ⟨Positive.map sharedMatrixEquiv.toNonUnitalStarAlgHom a, ?_⟩
    apply congrArg TraceCone.CuntzClass.mk
    apply Subtype.ext
    exact sharedMatrixEquiv.symm_apply_apply a.1

theorem shared_zero_sandwich (n : ℕ) :
    n • (0 : TraceCone.CuntzClass (TraceCone.MatrixLimit A)) ≤ 0 ∧
      (0 : TraceCone.CuntzClass (TraceCone.MatrixLimit A)) ≤ (n+1) • 0 := by
  simp

end Pureness
end

end OAI
