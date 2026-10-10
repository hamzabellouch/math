import OAI.Analysis.Pureness.Cuntz.CStarCuntz

namespace OAI
namespace CuntzPureness
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
  simp [cuntzSubequiv_zero_iff, zero_cuntzSubequiv]
end PositiveCuntzClass
end CuntzPureness

end OAI
