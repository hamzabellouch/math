import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransport
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRowsCoefficients

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistoryOccurrenceVariables Arithmetic.HistorySymbolicEncoding Characters.RationalHistory

theorem decoded_normalizedRows_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hcd : historyFrequencies sources seed V l c=historyFrequencies sources seed V l d)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside) :
    normalizedRows seed (decodeHistory sources seed V l a c) hc
      (decoded_tree_source_labels sources seed V l a c ha)=
    normalizedRows seed (decodeHistory sources seed V l b d) hd
      (decoded_tree_source_labels sources seed V l b d hb) := by
  rw [normalizedRows_eq_fixedCanonicalRows,normalizedRows_eq_fixedCanonicalRows,
    decoded_plan_eq sources seed V outside l a b c d ha hb hab hcd hc hd]

theorem decoded_normalizedRowFractions_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hcd : historyFrequencies sources seed V l c=historyFrequencies sources seed V l d)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside) (i : Internal seed l) :
    let ra := normalizedRows seed (decodeHistory sources seed V l a c) hc
      (decoded_tree_source_labels sources seed V l a c ha) i
    let rb := normalizedRows seed (decodeHistory sources seed V l b d) hd
      (decoded_tree_source_labels sources seed V l b d hb) i
    (ra.1.fraction,ra.2.fraction)=(rb.1.fraction,rb.2.fraction) := by
  have he := congrFun (decoded_normalizedRows_eq sources seed V outside l a b c d ha hb hab hcd hc hd) i
  exact congrArg (fun r => (r.1.fraction,r.2.fraction)) he

theorem decoded_actualRowPolynomials_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hcd : historyFrequencies sources seed V l c=historyFrequencies sources seed V l d)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside) (i : Internal seed l) :
    let H := decodeHistory sources seed V l a c
    let H' := decodeHistory sources seed V l b d
    let labels := decoded_tree_source_labels sources seed V l a c ha
    let labels' := decoded_tree_source_labels sources seed V l b d hb
    let f := (coordinateEquiv seed H labels).symm
    let g := (coordinateEquiv seed H' labels').symm
    let ra := Arithmetic.HistoryOccurrenceRows.canonical H hc (internalEquiv seed H labels i)
    let rb := Arithmetic.HistoryOccurrenceRows.canonical H' hd (internalEquiv seed H' labels' i)
    ((MvPolynomial.rename f ra.1.numerator,MvPolynomial.rename f ra.1.denominator),
      (MvPolynomial.rename f ra.2.numerator,MvPolynomial.rename f ra.2.denominator))=
    ((MvPolynomial.rename g rb.1.numerator,MvPolynomial.rename g rb.1.denominator),
      (MvPolynomial.rename g rb.2.numerator,MvPolynomial.rename g rb.2.denominator)) := by
  have he := decoded_normalizedRowFractions_eq sources seed V outside l a b c d ha hb hab hcd hc hd i
  simpa only [normalizedRows,Expr.fraction_rename,Expr.numerator,Expr.denominator] using he

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
