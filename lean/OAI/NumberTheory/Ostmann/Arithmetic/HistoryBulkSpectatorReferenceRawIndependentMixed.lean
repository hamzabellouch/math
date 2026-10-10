import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawIndependentUnit
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawMixedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction Conclusion CanonicalHistoryLeafBulk HistoryBulkProducts HistoryBulkDiagramParameters
open HistoryBulkSupportConverse HistoryBulkFrequencyTransport HistorySignedSpectatorCRT
open HistoryBulkSpectatorProduct HistoryCRTIntegration

theorem mixedTest_independent_source_eq_raw
    (b k l : ℕ) (bulk : PrimeSource) (top : Fin 3→PrimeSource)
    (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ) (outside : List ℕ)
    (a0 b0 a a' : State)
    (c c' : HistoryChoices (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x y : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x)
    (hx' : a'.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      y)
    (hbulk : ∀ u : Fin (2^l)×Fin (2*b),
      bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l y u.1 u.2 =
        bulkSamples (initialSourceFamily b k bulk top comp) (2*b) k l x (σ u).1 (σ u).2)
    (ha0 : Template.Matches (Template.current (Template.initial (2*b) k) l) a0.small)
    (hb0 : Template.Matches (Template.current (Template.initial (2*b) k) l) b0.small)
    (hf : a0.frequency=a.frequency) (hf' : b0.frequency=a'.frequency)
    (hfix : a0.small.map eraseBulkValue=a.small.map eraseBulkValue)
    (hfix' : b0.small.map eraseBulkValue=a'.small.map eraseBulkValue)
    (hs0 : (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a0 c).Supported V outside)
    (ht0 : (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l b0 c').Supported V outside)
    (hc : Nat.Coprime (bulkProduct a.small) outside.prod)
    (hc' : Nat.Coprime (bulkProduct a'.small) outside.prod)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (hg : ∀q∈outside,g q 0=0)
    (roots : MixedPair outside.prod) :
    mixedTest (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a0 c)
      (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l b0 c')
      hs0 ht0 hp hV σ g roots
      (sourceBulkUnits outside.prod (initialSourceFamily b k bulk top comp) (2*b) k l x)=
    residuePairSpectator g outside outside.prod
      (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a c)
      (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a' c')
      (roots.1,roots.2) := by
  classical
  by_cases hu : IsUnit roots.1
  · rw [mixedTest_eq_of_isUnit _ _ hs0 ht0 hp hV σ g roots _ hu,
      unitTest_independent_source_eq_raw b k l bulk top comp V outside a0 b0 a a' c c' σ x y
        hx hx' hbulk ha0 hb0 hf hf' hfix hfix' hs0 ht0 hc hc' hp hV g hg (hu.unit,roots.2)]
    simp only [IsUnit.unit_spec]
  · rw [mixedTest_nonunit _ _ hs0 ht0 hp hV σ g roots _ hu]
    symm
    let sources := initialSourceFamily b k bulk top comp
    let seed := Template.initial (2*b) k
    have ha : Template.Matches (Template.current seed l) a.small := by
      rw [hx]; exact Template.assignedSlots_matches _ _ _
    have hb : Template.Matches (Template.current seed l) a'.small := by
      rw [hx']; exact Template.assignedSlots_matches _ _ _
    have hap : a.PrimeSmall := by
      change ∀z∈a.small,z.value.Prime
      rw [hx]; exact assignedSlots_prime _ _ _
    have hbp : a'.PrimeSmall := by
      change ∀z∈a'.small,z.value.Prime
      rw [hx']; exact assignedSlots_prime _ _ _
    exact residuePair_zero_of_nonunit_static _ _
      (staticSkeleton_decode_redraw sources seed V l a0 a c ha0 ha hs0 hf hap)
      (staticSkeleton_decode_redraw sources seed V l b0 a' c' hb0 hb ht0 hf' hbp)
      hp hV
      (internal_outside_product_coprime_decode_redraw sources seed V l a0 a c hs0)
      (internal_outside_product_coprime_decode_redraw sources seed V l b0 a' c' ht0)
      g hg roots.1 roots.2 hu

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
