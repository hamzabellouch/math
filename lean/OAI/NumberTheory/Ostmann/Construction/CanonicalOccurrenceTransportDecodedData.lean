import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRows
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPairMaps
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRowsDecoded

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding

structure DecodedDraw (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) where
  root : State
  choices : HistoryChoices sources seed V l
  sourceMatch : Template.Matches (Template.current seed l) root.small
  supported : (decodeHistory sources seed V l root choices).Supported V outside

namespace DecodedDraw
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ→ℕ}
  {outside : List ℕ} {l : ℕ}

abbrev history (D : DecodedDraw sources seed V outside l) : History l :=
  decodeHistory sources seed V l D.root D.choices

theorem labels (D : DecodedDraw sources seed V outside l) : TreeSourceLabels seed D.history :=
  decoded_tree_source_labels sources seed V l D.root D.choices D.sourceMatch

def SameFrequencies (D E : DecodedDraw sources seed V outside l) : Prop :=
  D.root.frequency=E.root.frequency ∧
    historyFrequencies sources seed V l D.choices=historyFrequencies sources seed V l E.choices

theorem normalizedRows_eq {D E : DecodedDraw sources seed V outside l} (hDE : D.SameFrequencies E) :
    normalizedRows seed D.history D.supported D.labels=
      normalizedRows seed E.history E.supported E.labels :=
  decoded_normalizedRows_eq sources seed V outside l D.root E.root D.choices E.choices
    D.sourceMatch E.sourceMatch hDE.1 hDE.2 D.supported E.supported

theorem normalizedCode_eq {D E : DecodedDraw sources seed V outside l} (hDE : D.SameFrequencies E) :
    normalizedCode seed D.history D.supported D.labels=
      normalizedCode seed E.history E.supported E.labels :=
  decoded_normalizedCode_eq sources seed V outside l D.root E.root D.choices E.choices
    D.sourceMatch E.sourceMatch hDE.1 hDE.2 D.supported E.supported

end DecodedDraw
end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
