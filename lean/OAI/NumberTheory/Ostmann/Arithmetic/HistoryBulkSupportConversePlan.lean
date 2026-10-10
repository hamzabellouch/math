import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanLinear
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanSample

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySignedNumerators HistoryOccurrenceVariables HistorySymbolicEncoding

theorem reference_execute_rows_actual (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (i : Internal seed l)
    (hi : AncestorIntegralGuard (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i)) :
    let p := plan (decodeHistory sources seed V l a c) hs
    let ec := fixedCompensationCode seed l (fun j => Expr.atom (.inr (.inr j)))
    (fixedRows seed p (execute p (fixedRootCode seed l) ec)
      (execute p (fixedRootCode seed l) ec) i).1.rationalEval
        (newSourceSample sources seed V l b c hb Xp Xm)=
      (actual (decodeHistory sources seed V l b c) Xp Xm
        (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i):ℚ) := by
  let h := decodeHistory sources seed V l b c
  let hh := decoded_tree_source_labels sources seed V l b c hb
  let comp : InternalKey h→Expr (Coordinate seed l) :=
    fun j => .atom (.inr (.inr ((internalEquiv seed h hh).symm j)))
  have hc : ∀j,(comp j).rationalEval (newSourceSample sources seed V l b c hb Xp Xm)=
      ((internalSlot h j).value:ℚ) := by
    intro j
    change ((internalSlot h ((internalEquiv seed h hh) ((internalEquiv seed h hh).symm j))).value:ℚ)=_
    rw [Equiv.apply_symm_apply]
  have he := execute_rows_actual seed h hh _
    (decoded_reference_plan_fits sources seed V outside l a b c ha hb hab hs)
    (fixedRootCode seed l) comp (newSourceSample sources seed V l b c hb Xp Xm) Xp Xm
    rfl rfl (by simpa only [h,decodeHistory_root] using
      fixedRootCode_newSourceSample_small sources seed V l b c hb Xp Xm) hc i hi
  rw [show compensationCode h comp=fixedCompensationCode seed l
    (fun j => Expr.atom (.inr (.inr j))) from compensation_code_fixed seed h hh
      (fun j => (Expr.atom (.inr (.inr j)) : Expr (Coordinate seed l)))] at he
  exact he

theorem reference_row_actual (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (i : Internal seed l)
    (hi : AncestorIntegralGuard (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i)) :
    let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
      (decoded_tree_source_labels sources seed V l a c ha) i
    let x := newSourceSample sources seed V l b c hb Xp Xm
    (actual (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i):ℚ)=
        r.1.rationalEval x*(Xp:ℚ)+r.2.rationalEval x*(Xm:ℚ) := by
  have he := reference_execute_rows_actual sources seed V outside l a b c ha hb hab hs Xp Xm i hi
  have hl := fixedRows_execute_root_linear seed (plan (decodeHistory sources seed V l a c) hs)
    (newSourceSample sources seed V l b c hb Xp Xm) i
  dsimp only at he ⊢
  rw [normalizedRows_eq_fixedCanonicalRows]
  exact he.symm.trans hl

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
