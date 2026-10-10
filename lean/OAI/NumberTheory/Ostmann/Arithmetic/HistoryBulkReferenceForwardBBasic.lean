import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTests

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceForwardB
open Construction Construction.CanonicalOccurrenceTransport
open HistoryPairPattern HistoryPairRows HistoryOccurrenceVariables
open HistoryBulkSupportConverse HistoryBulkSupportConversePlan HistoryBulkReferenceTests
open HistorySignedResidueFactorization MvPolynomial

theorem indicator_eq_one_of_reference_lines
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a a' b b' : State) (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hb' : Template.Matches (Template.current seed l) b'.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (ks : (decodeHistory sources seed V l a' d).Supported V outside)
    (v : PairKey (decodeHistory sources seed V l a c) (decodeHistory sources seed V l a' d)→ℤ)
    (Xp Xm : ℤ)
    (hv : ∀q, v (leftMap _ _ q)=newIntegerSample sources seed V l b c hb Xp Xm
      ((decodedCoordinateEquiv sources seed V l a c ha).symm q))
    (hv' : ∀q, v (rightMap _ _ q)=newIntegerSample sources seed V l b' d hb' Xp Xm
      ((decodedCoordinateEquiv sources seed V l a' d ha').symm q))
    (ht : ∀i : Internal seed l,
      ((historyDraws sources seed V l c i).val:ℤ) ∣
        referenceLine sources seed V outside l a b c ha hb hs Xp Xm i ∧
      ¬((historyDraws sources seed V l c i).val:ℤ)^2 ∣
        referenceLine sources seed V outside l a b c ha hb hs Xp Xm i)
    (ht' : ∀i : Internal seed l,
      ((historyDraws sources seed V l d i).val:ℤ) ∣
        referenceLine sources seed V outside l a' b' d ha' hb' ks Xp Xm i ∧
      ¬((historyDraws sources seed V l d i).val:ℤ)^2 ∣
        referenceLine sources seed V outside l a' b' d ha' hb' ks Xp Xm i) :
    primeResidueIndicatorAt _ _ hs ks v (Xp,Xm)=1 := by
  have htst : finiteOwnPrimeLinesAt _ _ hs ks v (Xp,Xm) := by
    apply (finiteOwnPrimeLinesAt_intCast_iff _ _ hs ks v Xp Xm).mpr
    rintro (q | q)
    · obtain ⟨i,rfl⟩ := (internalEquiv seed _
        (decoded_tree_source_labels sources seed V l a c ha)).surjective q
      rw [left_line_eq_reference sources seed V outside l a b c ha hb hs _ ks v Xp Xm hv i]
      simpa only [slot, Sum.elim_inl, decoded_internalSlot_eq_historyDraw
        sources seed V l a c ha i] using ht i
    · obtain ⟨i,rfl⟩ := (internalEquiv seed _
        (decoded_tree_source_labels sources seed V l a' d ha')).surjective q
      rw [right_line_eq_reference sources seed V outside l a' b' d ha' hb' ks _ hs v Xp Xm hv' i]
      simpa only [slot, Sum.elim_inr, decoded_internalSlot_eq_historyDraw
        sources seed V l a' d ha' i] using ht' i
  classical
  simp only [primeResidueIndicatorAt,guardIndicator,ite_eq_left htst]

end Ostmann.Arithmetic.HistoryBulkReferenceForwardB

end

end OAI
