import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceForwardBGuards
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTests

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardB
open Construction Construction.CanonicalOccurrenceTransport
open HistoryOccurrenceVariables HistorySignedNumerators HistoryBulkSupportConverse
open HistoryBulkSupportConversePlan HistorySupportReduction HistoryBulkReferenceForwardBGuards

theorem reference_lines_squares_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (ht : (decodeHistory sources seed V l b c).Supported V outside)
    (hlarge : LargePrimes V (decodeHistory sources seed V l b c))
    (hx : ReferenceAncestorUnits sources seed V l b c hb b.giantPlus b.giantMinus)
    (hV : ∀i : Internal seed l, ∀j≤l,V j<(historyDraws sources seed V l c i).val) :
    ∀ i : Internal seed l,
      ((historyDraws sources seed V l c i).val:ℤ) ∣
        referenceLine sources seed V outside l a b c ha hb hs b.giantPlus b.giantMinus i ∧
      ¬((historyDraws sources seed V l c i).val:ℤ)^2 ∣
        referenceLine sources seed V outside l a b c ha hb hs b.giantPlus b.giantMinus i := by
  intro i
  let j := internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i
  let : Fact (historyDraws sources seed V l c i).val.Prime :=
    ⟨(sources (internalSource seed i).origin).prime _ (historyDraws sources seed V l c i).property⟩
  have hroot : (decodeHistory sources seed V l b c).root=b := decodeHistory_root _ _ _ _ _ _
  have hi := rebuild_integralGuard_of_supported _ ht
  rw [hroot] at hi
  have hai := ancestorIntegralGuard_of_integralGuard _ _ _ hi j
  have hd := actual_divisible_of_supported _ ht j
  have hsq := actual_square_not_dvd_of_supported _ ht hlarge j
  rw [hroot] at hd hsq
  dsimp only [j] at hd hsq
  rw [decoded_internalSlot_eq_historyDraw sources seed V l b c hb i] at hd hsq
  have he1 := reference_row_power_dvd_iff sources seed V outside l a b c ha hb hab hs
    b.giantPlus b.giantMinus i hai (historyDraws sources seed V l c i).val 1 (hx i) (hV i)
  have he2 := reference_row_power_dvd_iff sources seed V outside l a b c ha hb hab hs
    b.giantPlus b.giantMinus i hai (historyDraws sources seed V l c i).val 2 (hx i) (hV i)
  constructor
  · simpa only [pow_one, referenceLine] using he1.mp (by simpa only [pow_one] using hd)
  · simpa only [referenceLine] using (not_congr he2).mp hsq

theorem reference_lines_squares_of_supported_source
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (ht : (decodeHistory sources seed V l b c).Supported V outside)
    (hroot : ∀q∈b.small,sourceMass sources q≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hx : ReferenceAncestorUnits sources seed V l b c hb b.giantPlus b.giantMinus) :
    ∀ i : Internal seed l,
      ((historyDraws sources seed V l c i).val:ℤ) ∣
        referenceLine sources seed V outside l a b c ha hb hs b.giantPlus b.giantMinus i ∧
      ¬((historyDraws sources seed V l c i).val:ℤ)^2 ∣
        referenceLine sources seed V outside l a b c ha hb hs b.giantPlus b.giantMinus i :=
  reference_lines_squares_of_supported sources seed V outside l a b c ha hb hab hs ht
    (decoded_largePrimes sources seed V l b c hb hroot hc hfreq) hx
    (own_frequency_bounds_of_mass sources seed V l b c hb hc hfreq)

end Ostmann.Arithmetic.HistoryBulkReferenceForwardB

end

end OAI
