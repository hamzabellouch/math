import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanOwn
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSourceUnits
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction Construction.CanonicalOccurrenceTransport
open HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables
open HistorySignedSupportReduction HistorySignedResidueFactorization
open HistorySymbolicEncoding HistoryBulkSupportConversePlan HistorySupportReduction
open Characters.RationalHistory ClearedCoefficientFlags MvPolynomial

def referenceLine (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (i : Internal seed l) : ℤ :=
  let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
    (decoded_tree_source_labels sources seed V l a c ha) i
  let z := newIntegerSample sources seed V l b c hb Xp Xm
  eval z (leftCoefficient r.1 r.2)*Xp+eval z (rightCoefficient r.1 r.2)*Xm

def ReferenceAncestorUnits (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small) (Xp Xm : ℤ) : Prop :=
  ∀i : Internal seed l, ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
    CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
    (newIntegerSample sources seed V l b c hb Xp Xm (.inr q) :
      ZMod (historyDraws sources seed V l c i).val)≠0

theorem own_frequency_bounds_of_mass (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (b : State) (c : HistoryChoices sources seed V l)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j)) :
    ∀i : Internal seed l,∀j≤l,V j<(historyDraws sources seed V l c i).val := by
  intro i j hj
  have hm := HistoryRepresentativeSourceSeparation.decoded_internalSlot_mass
    sources seed V l b c hc
    (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i)
  have he := sourceMass_value_gt (hfreq j hj) hm
  simpa only [decoded_internalSlot_eq_historyDraw sources seed V l b c hb i] using he

theorem guardedOwn_of_referenceLines
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small) (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) (Xp Xm : ℤ)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hx : ReferenceAncestorUnits sources seed V l b c hb Xp Xm)
    (hlines : ∀i : Internal seed l, ((historyDraws sources seed V l c i).val:ℤ) ∣
      referenceLine sources seed V outside l a b c ha hb hs Xp Xm i) :
    GuardedOwnDivisibility (decodeHistory sources seed V l b c) Xp Xm :=
  reference_guardedOwnDivisibility_of_lines sources seed V outside l a b c ha hb hab hs Xp Xm
    hx (own_frequency_bounds_of_mass sources seed V l b c hb hc hfreq) hlines

theorem squareExclusions_of_referenceLines
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small) (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) (Xp Xm : ℤ)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j))
    (hx : ReferenceAncestorUnits sources seed V l b c hb Xp Xm)
    (hi : (rebuild (decodeHistory sources seed V l b c) Xp Xm).IntegralGuard)
    (hlines : ∀i : Internal seed l, ¬((historyDraws sources seed V l c i).val:ℤ)^2 ∣
      referenceLine sources seed V outside l a b c ha hb hs Xp Xm i) :
    ∀i : InternalKey (decodeHistory sources seed V l b c),
      ¬((internalSlot _ i).value:ℤ)^2 ∣ actual _ Xp Xm i := by
  intro j
  obtain ⟨i,rfl⟩ := (internalEquiv seed _
    (decoded_tree_source_labels sources seed V l b c hb)).surjective j
  exact reference_own_square_exclusion sources seed V outside l a b c ha hb hab hs Xp Xm i
    (ancestorIntegralGuard_of_integralGuard _ Xp Xm hi _)
    (hx i) (own_frequency_bounds_of_mass sources seed V l b c hb hc hfreq i) (hlines i)

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
