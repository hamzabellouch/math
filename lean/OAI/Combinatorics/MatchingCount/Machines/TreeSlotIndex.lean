import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeNumberedCodec

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeTyped.Numbered Replica.Ladder

def coordinateEquiv (T q : ℕ) : Slot T q ≃ Fin ((T+1)*q) :=
  ({toFun:=ofLex,invFun:=toLex,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl} : Slot T q≃Fin (T+1)×Fin q).trans finProdFinEquiv
lemma coordinate_le {T q : ℕ} (a b : Slot T q) : coordinateEquiv T q a≤coordinateEquiv T q b ↔ a≤b := by
  change (ofLex a).2.val+q*(ofLex a).1.val≤(ofLex b).2.val+q*(ofLex b).1.val ↔ a≤b
  rw [Prod.Lex.le_iff]
  have ha:=(ofLex a).2.isLt
  have hb:=(ofLex b).2.isLt
  change _ ↔ ((ofLex a).1.val<(ofLex b).1.val ∨ (ofLex a).1=(ofLex b).1 ∧ (ofLex a).2.val≤(ofLex b).2.val)
  constructor
  · intro h
    by_cases hlt : (ofLex a).1.val<(ofLex b).1.val
    · exact Or.inl hlt
    · have hge : (ofLex b).1.val≤(ofLex a).1.val := Nat.le_of_not_gt hlt
      have he : (ofLex a).1.val=(ofLex b).1.val := by
        by_contra hh
        have hs : (ofLex b).1.val+1≤(ofLex a).1.val := by omega
        have hm:=Nat.mul_le_mul_left q hs
        nlinarith
      exact Or.inr ⟨Fin.ext he,by rw [he] at h; omega⟩
  · rintro (h|⟨h,h'⟩)
    · have hm:=Nat.mul_le_mul_left q h
      nlinarith
    · rw [h]; omega

def coordinateOrderIso (T q : ℕ) : Slot T q ≃o Fin ((T+1)*q) :=
  { coordinateEquiv T q with map_rel_iff' := fun {a b}=>coordinate_le a b }
lemma slot_card (T q : ℕ) : Fintype.card (Slot T q)=(T+1)*q := by simp [Slot]
def numberOrderIso (T q : ℕ) : Slot T q ≃o Fin ((T+1)*q) := by
  let e : Slot T q ≃o Fin (Fintype.card (Slot T q)) :=
    { toEquiv := (UnitRefresh.orderedEnum (Slot T q)).symm
      map_rel_iff' := by
        intro a b
        change ((UnitRefresh.orderedEnum (Slot T q)).symm a).val ≤
          ((UnitRefresh.orderedEnum (Slot T q)).symm b).val ↔ a ≤ b
        exact index_le a b }
  exact e.trans (Fin.castOrderIso (slot_card T q))
lemma slot_index {T q : ℕ} (x : Slot T q) : index x=q*rank x+(ofLex x).2.val := by
  have he : numberOrderIso T q=coordinateOrderIso T q := Subsingleton.elim _ _
  have h:=congrArg (fun e : Slot T q≃o Fin ((T+1)*q)=>(e x).val) he
  change index x=(ofLex x).2.val+q*(ofLex x).1.val at h
  simpa only [rank,Nat.add_comm] using h
lemma slot_default_zero (T q : ℕ) (hq : 0<q) :
    index (toLex ((0 : Fin (T+1)),(⟨0,hq⟩ : Fin q)))=0 := by
  rw [slot_index]
  rfl
lemma slot_index_div {T q : ℕ} (x : Slot T q) : index x/q=rank x := by
  rw [slot_index,Nat.add_comm,Nat.add_mul_div_left]
  · simp [Nat.div_eq_of_lt (ofLex x).2.isLt]
  · exact Nat.zero_lt_of_lt (ofLex x).2.isLt
end MatchingFPRAS.NumericLadder

end OAI
