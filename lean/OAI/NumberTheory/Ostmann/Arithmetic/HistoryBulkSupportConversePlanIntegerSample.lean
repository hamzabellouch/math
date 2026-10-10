import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanSample

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory

def newIntegerSample (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) :
    Coordinate seed l→ℤ
  | .inl false => Xp
  | .inl true => Xm
  | .inr (.inl i) => (b.small.get (finCongr (Template.matches_length hb).symm i)).value
  | .inr (.inr i) => (historyDraws sources seed V l c i).val

theorem newIntegerSample_cast (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) :
    (fun i => (newIntegerSample sources seed V l b c hb Xp Xm i:ℚ))=
      newSourceSample sources seed V l b c hb Xp Xm := by
  funext i
  rcases i with i | i | i
  · cases i <;> rfl
  · simp only [newIntegerSample,Int.cast_natCast,newSourceSample_small]
  · simp only [newIntegerSample,Int.cast_natCast,newSourceSample_internal]

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
