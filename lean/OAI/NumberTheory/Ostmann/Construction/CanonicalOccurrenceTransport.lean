import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportCoefficients
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPlan

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport

theorem decoded_normalizedCode_eq (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (a b : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hcd : historyFrequencies sources seed V l c=historyFrequencies sources seed V l d)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside) :
    normalizedCode seed (decodeHistory sources seed V l a c) hc
      (decoded_tree_source_labels sources seed V l a c ha)=
    normalizedCode seed (decodeHistory sources seed V l b d) hd
      (decoded_tree_source_labels sources seed V l b d hb) := by
  rw [normalizedCode_eq_execute,normalizedCode_eq_execute,
    decoded_plan_eq sources seed V outside l a b c d ha hb hab hcd hc hd]

theorem decoded_normalizedCoefficientCode_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hcd : historyFrequencies sources seed V l c=historyFrequencies sources seed V l d)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside) (second : Bool) :
    normalizedCoefficientCode seed (decodeHistory sources seed V l a c) hc
      (decoded_tree_source_labels sources seed V l a c ha) second=
    normalizedCoefficientCode seed (decodeHistory sources seed V l b d) hd
      (decoded_tree_source_labels sources seed V l b d hb) second := by
  rw [normalizedCoefficientCode_eq_execute,normalizedCoefficientCode_eq_execute,
    decoded_plan_eq sources seed V outside l a b c d ha hb hab hcd hc hd]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
