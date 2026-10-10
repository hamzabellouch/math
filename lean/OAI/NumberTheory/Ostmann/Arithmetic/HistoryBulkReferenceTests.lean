import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTests
open Construction Construction.CanonicalOccurrenceTransport
open HistorySymbolicEncoding HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan

theorem left_reference_lines_squares_of_B
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (k : History l) (ks : k.Supported V outside)
    (v : PairKey (decodeHistory sources seed V l a c) k → ℤ) (Xp Xm : ℤ)
    (hv : ∀ q, v (leftMap _ k q) =
      newIntegerSample sources seed V l b c hb Xp Xm
        ((decodedCoordinateEquiv sources seed V l a c ha).symm q))
    (hB : primeResidueIndicatorAt _ k hs ks v (Xp,Xm) ≠ 0) :
    ∀ i : Internal seed l,
      ((historyDraws sources seed V l c i).val : ℤ) ∣
        referenceLine sources seed V outside l a b c ha hb hs Xp Xm i ∧
      ¬((historyDraws sources seed V l c i).val : ℤ)^2 ∣
        referenceLine sources seed V outside l a b c ha hb hs Xp Xm i := by
  intro i
  have hi := tests_of_primeResidueIndicatorAt_ne_zero _ k hs ks v Xp Xm hB
    (.inl (internalEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha) i))
  have he := left_line_eq_reference sources seed V outside l a b c ha hb hs k ks v Xp Xm hv i
  rw [he] at hi
  simpa only [slot, Sum.elim_inl, decoded_internalSlot_eq_historyDraw
    sources seed V l a c ha i] using hi

theorem right_reference_lines_squares_of_B
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (ks : (decodeHistory sources seed V l a c).Supported V outside)
    (h : History l) (hs : h.Supported V outside)
    (v : PairKey h (decodeHistory sources seed V l a c) → ℤ) (Xp Xm : ℤ)
    (hv : ∀ q, v (rightMap h _ q) =
      newIntegerSample sources seed V l b c hb Xp Xm
        ((decodedCoordinateEquiv sources seed V l a c ha).symm q))
    (hB : primeResidueIndicatorAt h _ hs ks v (Xp,Xm) ≠ 0) :
    ∀ i : Internal seed l,
      ((historyDraws sources seed V l c i).val : ℤ) ∣
        referenceLine sources seed V outside l a b c ha hb ks Xp Xm i ∧
      ¬((historyDraws sources seed V l c i).val : ℤ)^2 ∣
        referenceLine sources seed V outside l a b c ha hb ks Xp Xm i := by
  intro i
  have hi := tests_of_primeResidueIndicatorAt_ne_zero h _ hs ks v Xp Xm hB
    (.inr (internalEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha) i))
  have he := right_line_eq_reference sources seed V outside l a b c ha hb ks h hs v Xp Xm hv i
  rw [he] at hi
  simpa only [slot, Sum.elim_inr, decoded_internalSlot_eq_historyDraw
    sources seed V l a c ha i] using hi

end Ostmann.Arithmetic.HistoryBulkReferenceTests

end

end OAI
