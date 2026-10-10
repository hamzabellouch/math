import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeXi
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesValues
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalar
import OAI.NumberTheory.Ostmann.Construction.SmoothHistoryFactor

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedXiTransport
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistorySignedDecode

def giantState (a : State) (Xp Xm : ℤ) : State :=
  ⟨a.frequency,Xp.toNat,Xm.toNat,a.small⟩

theorem decoded_internalOccurrences_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a a' : State) (c : HistoryChoices sources seed V l) :
    (decodeHistory sources seed V l a c).internalOccurrences=
      (decodeHistory sources seed V l a' c).internalOccurrences := by
  induction l generalizing a a' with
  | zero => rfl
  | succ l ih =>
    simp only [decodeHistory,History.internalOccurrences]
    simp only [List.append_assoc]
    exact congrArg (List.append _) (congrArg₂ List.append
      (ih _ _ c.2.2.2.1) (ih _ _ c.2.2.2.2))

theorem decoded_compensationProduct_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a a' : State) (c : HistoryChoices sources seed V l) :
    (decodeHistory sources seed V l a c).compensationProduct=
      (decodeHistory sources seed V l a' c).compensationProduct := by
  simp only [History.compensationProduct,decoded_internalOccurrences_eq sources seed V l a a' c]

theorem signedGiantSample_coordinate_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (Xp Xm : ℤ) (hp : 0≤Xp) (hm : 0≤Xm) (i : Coordinate seed l) :
    signedGiantSample (decodeHistory sources seed V l a c) Xp Xm
      (coordinateEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha) i)=
    (integerSample (decodeHistory sources seed V l (giantState a Xp Xm) c)
      (coordinateEquiv seed _ (decoded_tree_source_labels sources seed V l (giantState a Xp Xm) c ha) i):ℝ) := by
  rcases i with b | i | i
  · cases b <;> simp [coordinateEquiv,signedGiantSample,integerSample,giantState,hp,hm] <;> rfl
  · simp [coordinateEquiv,Equiv.sumCongr,signedGiantSample,integerSample,giantState]
    rfl
  · have hi := (decoded_internalSlot_eq_historyDraw sources seed V l a c ha i).trans
      (decoded_internalSlot_eq_historyDraw sources seed V l (giantState a Xp Xm) c ha i).symm
    simpa [coordinateEquiv,signedGiantSample,integerSample] using
      congrArg (fun n : ℕ => (n:ℝ)) hi

end Ostmann.Arithmetic.HistorySignedXiTransport

end

end OAI
