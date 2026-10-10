import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySignedNumerators HistoryOccurrenceVariables HistorySymbolicEncoding

def newSourceSample (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) :
    Coordinate seed l→ℚ :=
  signedRationalSample (decodeHistory sources seed V l b c) Xp Xm ∘
    decodedCoordinateEquiv sources seed V l b c hb

@[simp] theorem newSourceSample_plus (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) :
    newSourceSample sources seed V l b c hb Xp Xm (.inl false)=(Xp:ℚ) := rfl

@[simp] theorem newSourceSample_minus (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) :
    newSourceSample sources seed V l b c hb Xp Xm (.inl true)=(Xm:ℚ) := rfl

@[simp] theorem newSourceSample_small (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ)
    (i : Fin (Template.current seed l).length) :
    newSourceSample sources seed V l b c hb Xp Xm (.inr (.inl i))=
      ((b.small.get (finCongr (Template.matches_length hb).symm i)).value:ℚ) := by
  cases l <;> rfl

@[simp] theorem newSourceSample_internal (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ)
    (i : Internal seed l) :
    newSourceSample sources seed V l b c hb Xp Xm (.inr (.inr i))=
      ((historyDraws sources seed V l c i).val:ℚ) := by
  change ((internalSlot (decodeHistory sources seed V l b c)
    (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i)).value:ℚ)=_
  rw [decoded_internalSlot_eq_historyDraw sources seed V l b c hb i]

 theorem fixedRootCode_newSourceSample_small (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) :
    (fixedRootCode seed l).small.map
      (fun e => e.rationalEval (newSourceSample sources seed V l b c hb Xp Xm))=
      b.small.map (fun a => (a.value:ℚ)) := by
  simp only [fixedRootCode,List.map_ofFn,Function.comp_def,Expr.rationalEval,newSourceSample_small]
  calc
    _ = List.ofFn (fun i : Fin b.small.length => ((b.small.get i).value:ℚ)) :=
      ofFn_finCongr (Template.matches_length hb).symm (fun i => ((b.small.get i).value:ℚ))
    _ = _ := List.ofFn_getElem_eq_map b.small (fun a => (a.value:ℚ))

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
