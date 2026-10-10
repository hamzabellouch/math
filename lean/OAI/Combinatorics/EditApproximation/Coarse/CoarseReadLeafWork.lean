import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadCore
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandGuardWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Compare one tagged source letter with a framed target lookup. -/


theorem coarseLetterMatchWithWork_value (actual : Option (Option ℕ)) (wanted : Option ℕ) :
    (coarseLetterMatchWithWork actual wanted).1 = true ↔ actual = some wanted := by
  cases actual with
  | none => cases wanted <;> simp only [coarseLetterMatchWithWork, Bool.false_eq_true, reduceCtorEq]
  | some actual =>
    cases actual <;> cases wanted <;>
      simp only [coarseLetterMatchWithWork, naturalEqualWithWork_value, Option.some.injEq,
        Bool.false_eq_true, reduceCtorEq, iff_self]

theorem coarseLetterMatchWithWork_cost (actual : Option (Option ℕ)) (wanted : Option ℕ)
    (S : ℕ) (ha : ∀ a, actual = some (some a) → Nat.size a ≤ S)
    (hw : ∀ b, wanted = some b → Nat.size b ≤ S) :
    (coarseLetterMatchWithWork actual wanted).2 ≤ 8 * S + 2 := by
  cases actual with
  | none => cases wanted <;> simp only [coarseLetterMatchWithWork] <;> omega
  | some actual =>
    cases actual with
    | none => cases wanted <;> simp only [coarseLetterMatchWithWork] <;> omega
    | some a =>
      cases wanted with
      | none => simp only [coarseLetterMatchWithWork]; omega
      | some b => exact naturalEqualWithWork_cost a b S (ha a rfl) (hw b rfl)

theorem coarseFramedRead_symbol_mem (k n : ℕ) (target : List ℕ) (i a : ℕ)
    (h : coarseFramedRead k n target i = some (some a)) : a ∈ target := by
  unfold coarseFramedRead at h
  split_ifs at h
  · exact List.mem_of_getElem? (Option.some.inj h)

namespace BinaryFraction

/-- The leaf lookup explicitly adds the shift, reads the indexed frame and
compares the stored symbol bits. -/


theorem coarseReadShiftWithWork_value (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    (coarseReadShiftWithWork k n target letter start shift).1 =
      coarseReadShiftCost k n target letter start shift := by
  cases letter with
  | none => rfl
  | some letter =>
    simp only [coarseReadShiftWithWork, binaryNaturalAddWithWork_value,
      coarseFramedReadWithWork_value, coarseReadShiftCost,
      coarseLetterMatchWithWork_value]

theorem coarseReadShiftWithWork_cost (k n : ℕ) (target : List ℕ)
    (letter : Option (Option ℕ)) (start : ℕ) (shift : Fin (2 * k + 1)) (A S : ℕ)
    (hk : Nat.size k ≤ A) (hn : Nat.size n ≤ A) (hs : Nat.size start ≤ A)
    (hi : Nat.size shift.val ≤ A) (ht : ∀ a ∈ target, Nat.size a ≤ S)
    (hl : ∀ a, letter = some (some a) → Nat.size a ≤ S) :
    (coarseReadShiftWithWork k n target letter start shift).2 ≤ 200 * (A + 3) + 8 * S := by
  cases letter with
  | none => simp only [coarseReadShiftWithWork]; omega
  | some letter =>
    have hp := binaryNaturalAdd_size_le start shift.val
    have hpos : Nat.size (start + shift.val) ≤ A + 2 := hp.trans (Nat.add_le_add_right (max_le hs hi) 2)
    have hf := coarseFramedReadWithWork_cost k n target (start + shift.val) (A + 2)
      (by omega) (by omega) hpos
    have hm := coarseLetterMatchWithWork_cost
      (coarseFramedReadWithWork k n target (start + shift.val)).1 letter S
      (fun a ha => ht a (coarseFramedRead_symbol_mem k n target (start + shift.val) a
        ((coarseFramedReadWithWork_value k n target _).symm.trans ha)))
      (fun a ha => hl a (congrArg some ha))
    have ha := binaryNaturalAddWithWork_cost start shift.val
    simp only [coarseReadShiftWithWork, binaryNaturalAddWithWork_value]
    omega

end BinaryFraction
end EditApproximation

end OAI
