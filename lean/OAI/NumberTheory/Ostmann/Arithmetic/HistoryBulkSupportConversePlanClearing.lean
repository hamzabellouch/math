import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlan
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanIntegerSample
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanRegular
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrimeSquareSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySignedNumerators HistoryOccurrenceVariables HistorySymbolicEncoding
open ClearedCoefficientFlags MvPolynomial

theorem normalizedRows_regular_rat (seed : List SourceSlot) {l : ℕ}
    {V : ℕ→ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) (i : Internal seed l) (z : Coordinate seed l→ℤ)
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        z (.inr q)≠0) :
    (normalizedRows seed h hs hh i).1.FieldRegularAt (fun q => (z q:ℚ)) ∧
      (normalizedRows seed h hs hh i).2.FieldRegularAt (fun q => (z q:ℚ)) := by
  apply normalizedRows_regular seed h hs hh i
  · intro q hq
    exact Int.cast_ne_zero.mpr (hx q hq)
  · intro s hs'
    exact Int.cast_ne_zero.mpr (History.supported_frequency_bounds hs s hs').1

theorem normalizedRows_denominator_ne_zero (seed : List SourceSlot) {l : ℕ}
    {V : ℕ→ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) (i : Internal seed l) (z : Coordinate seed l→ℤ)
    (p : ℕ) [Fact p.Prime]
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        (z (.inr q):ZMod p)≠0)
    (hV : ∀j≤l,V j<p) :
    (eval z (commonDenominator (normalizedRows seed h hs hh i).1
      (normalizedRows seed h hs hh i).2):ZMod p)≠0 := by
  have hr := normalizedRows_regular seed h hs hh i (fun q => (z q:ZMod p)) hx
    (HistoryPrimeRows.frequency_units h hs p hV)
  have hd := (coefficients_cleared (normalizedRows seed h hs hh i).1
    (normalizedRows seed h hs hh i).2 _ hr.1 hr.2).1
  rwa [Expr.eval₂_cast_int] at hd

theorem reference_row_integer_cleared (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (i : Internal seed l)
    (hi : AncestorIntegralGuard (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i))
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        newIntegerSample sources seed V l b c hb Xp Xm (.inr q)≠0) :
    let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
      (decoded_tree_source_labels sources seed V l a c ha) i
    let z := newIntegerSample sources seed V l b c hb Xp Xm
    eval z (commonDenominator r.1 r.2)*
      actual (decodeHistory sources seed V l b c) Xp Xm
        (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i)=
      eval z (leftCoefficient r.1 r.2)*Xp+eval z (rightCoefficient r.1 r.2)*Xm := by
  let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
    (decoded_tree_source_labels sources seed V l a c ha) i
  let z := newIntegerSample sources seed V l b c hb Xp Xm
  have hr := normalizedRows_regular_rat seed (decodeHistory sources seed V l a c) hs
    (decoded_tree_source_labels sources seed V l a c ha) i z hx
  have hc := coefficients_cleared r.1 r.2 (fun q => (z q:ℚ)) hr.1 hr.2
  simp only [Expr.fieldEval_rat] at hc
  have hline :
      (actual (decodeHistory sources seed V l b c) Xp Xm
        (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i):ℚ)=
        r.1.rationalEval (fun q => (z q:ℚ))*(Xp:ℚ)+
          r.2.rationalEval (fun q => (z q:ℚ))*(Xm:ℚ) := by
    simpa only [r,z,newIntegerSample_cast] using
      reference_row_actual sources seed V outside l a b c ha hb hab hs Xp Xm i hi
  have hQ : eval₂ (Int.castRingHom ℚ) (fun q => (z q:ℚ)) (commonDenominator r.1 r.2)*
      (actual (decodeHistory sources seed V l b c) Xp Xm
        (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i):ℚ)=
      eval₂ (Int.castRingHom ℚ) (fun q => (z q:ℚ)) (leftCoefficient r.1 r.2)*(Xp:ℚ)+
      eval₂ (Int.castRingHom ℚ) (fun q => (z q:ℚ)) (rightCoefficient r.1 r.2)*(Xm:ℚ) := by
    rw [hline,hc.2.1,hc.2.2]
    ring
  simp only [Expr.eval₂_cast_int] at hQ
  apply Int.cast_injective (α:=ℚ)
  simpa only [Int.cast_mul,Int.cast_add] using hQ

theorem reference_row_power_dvd_iff (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (i : Internal seed l)
    (hi : AncestorIntegralGuard (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i))
    (p n : ℕ) [Fact p.Prime]
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        (newIntegerSample sources seed V l b c hb Xp Xm (.inr q):ZMod p)≠0)
    (hV : ∀j≤l,V j<p) :
    let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
      (decoded_tree_source_labels sources seed V l a c ha) i
    let z := newIntegerSample sources seed V l b c hb Xp Xm
    (p:ℤ)^n ∣ actual (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i) ↔
      (p:ℤ)^n ∣ eval z (leftCoefficient r.1 r.2)*Xp+
        eval z (rightCoefficient r.1 r.2)*Xm := by
  have hxZ : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        newIntegerSample sources seed V l b c hb Xp Xm (.inr q)≠0 := by
    intro q hq hz
    exact hx q hq (by rw [hz,Int.cast_zero])
  exact HistoryPrimeSquareSupport.power_dvd_cleared_iff p n _ _ _ _ Xp Xm
    (normalizedRows_denominator_ne_zero seed (decodeHistory sources seed V l a c) hs
      (decoded_tree_source_labels sources seed V l a c ha) i
      (newIntegerSample sources seed V l b c hb Xp Xm) p hx hV)
    (reference_row_integer_cleared sources seed V outside l a b c ha hb hab hs Xp Xm i hi hxZ)

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
