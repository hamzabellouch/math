import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanClearing
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuards

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction Construction.CanonicalOccurrenceTransport Characters.RationalHistory
open HistorySignedNumerators HistoryOccurrenceVariables ClearedCoefficientFlags MvPolynomial

theorem reference_guardedOwnDivisibility_of_lines
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) (Xp Xm : ℤ)
    (hx : ∀i : Internal seed l, ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
      (newIntegerSample sources seed V l b c hb Xp Xm (.inr q) :
        ZMod (historyDraws sources seed V l c i).val)≠0)
    (hV : ∀i : Internal seed l, ∀j≤l,V j<(historyDraws sources seed V l c i).val)
    (hlines : ∀i : Internal seed l,
      let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
        (decoded_tree_source_labels sources seed V l a c ha) i
      let z := newIntegerSample sources seed V l b c hb Xp Xm
      ((historyDraws sources seed V l c i).val:ℤ) ∣
        eval z (leftCoefficient r.1 r.2)*Xp+eval z (rightCoefficient r.1 r.2)*Xm) :
    GuardedOwnDivisibility (decodeHistory sources seed V l b c) Xp Xm := by
  intro j hj
  obtain ⟨i,rfl⟩ := (internalEquiv seed _
    (decoded_tree_source_labels sources seed V l b c hb)).surjective j
  let : Fact (historyDraws sources seed V l c i).val.Prime :=
    ⟨(sources (internalSource seed i).origin).prime _ (historyDraws sources seed V l c i).property⟩
  have he := reference_row_power_dvd_iff sources seed V outside l a b c ha hb hab hs
    Xp Xm i hj (historyDraws sources seed V l c i).val 1 (hx i) (hV i)
  simp only [pow_one] at he
  rw [decoded_internalSlot_eq_historyDraw sources seed V l b c hb i]
  exact he.mpr (hlines i)

theorem reference_own_square_exclusion
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hab : a.frequency=b.frequency)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (Xp Xm : ℤ) (i : Internal seed l)
    (hi : AncestorIntegralGuard (decodeHistory sources seed V l b c) Xp Xm
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i))
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
      (newIntegerSample sources seed V l b c hb Xp Xm (.inr q) :
        ZMod (historyDraws sources seed V l c i).val)≠0)
    (hV : ∀j≤l,V j<(historyDraws sources seed V l c i).val)
    (hline :
      let r := normalizedRows seed (decodeHistory sources seed V l a c) hs
        (decoded_tree_source_labels sources seed V l a c ha) i
      let z := newIntegerSample sources seed V l b c hb Xp Xm
      ¬((historyDraws sources seed V l c i).val:ℤ)^2 ∣
        eval z (leftCoefficient r.1 r.2)*Xp+eval z (rightCoefficient r.1 r.2)*Xm) :
    ¬((internalSlot (decodeHistory sources seed V l b c)
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i)).value:ℤ)^2 ∣
      actual (decodeHistory sources seed V l b c) Xp Xm
        (internalEquiv seed _ (decoded_tree_source_labels sources seed V l b c hb) i) := by
  let : Fact (historyDraws sources seed V l c i).val.Prime :=
    ⟨(sources (internalSource seed i).origin).prime _ (historyDraws sources seed V l c i).property⟩
  rw [decoded_internalSlot_eq_historyDraw sources seed V l b c hb i]
  exact fun hn => hline ((reference_row_power_dvd_iff sources seed V outside l a b c
    ha hb hab hs Xp Xm i hi (historyDraws sources seed V l c i).val 2 hx hV).mp hn)

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
