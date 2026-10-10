import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawProduct
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawSamples

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction Conclusion CanonicalHistoryLeafBulk HistoryBulkProducts HistoryBulkDiagramParameters
open HistoryBulkSupportConverse HistoryBulkFrequencyTransport HistorySignedSpectatorCRT
open HistoryBulkSpectatorProduct HistoryCRTIntegration

theorem unitTest_source_eq_raw
    (b k l : ℕ) (bulk : PrimeSource) (top : Fin 3→PrimeSource)
    (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ) (outside : List ℕ)
    (a0 b0 a a' : State)
    (c c' : HistoryChoices (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x)
    (hx' : a'.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
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
    (roots : UnitPair outside.prod) :
    unitTest (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a0 c)
      (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l b0 c')
      hs0 ht0 hp hV σ g roots
      (sourceBulkUnits outside.prod (initialSourceFamily b k bulk top comp) (2*b) k l x)=
    residuePairSpectator g outside outside.prod
      (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a c)
      (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a' c')
      (roots.1,roots.2) := by
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
  have hn := staticSkeleton_decode_redraw sources seed V l a0 a c ha0 ha hs0 hf hap
  have kn := staticSkeleton_decode_redraw sources seed V l b0 a' c' hb0 hb ht0 hf' hbp
  have hcx : Nat.Coprime (bulkProduct (assignedSlots sources (Template.current seed l) x)) outside.prod := by
    rw [←hx]; exact hc
  apply unitTest_eq_raw_of_leaves _ _ _ _ hs0 ht0 hn kn
    (sameFrequencyData_decode sources seed V l a0 a c hf hfix)
    (sameFrequencyData_decode sources seed V l b0 a' c' hf' hfix')
    (by simpa only [decodeHistory_root] using fixedProduct_eq_of_erase_eq hfix)
    (by simpa only [decodeHistory_root] using fixedProduct_eq_of_erase_eq hfix')
    (by simpa only [decodeHistory_root] using hc)
    (by simpa only [decodeHistory_root] using hc')
    (internal_outside_product_coprime_decode_redraw sources seed V l a0 a c hs0)
    (internal_outside_product_coprime_decode_redraw sources seed V l b0 a' c' ht0)
    hp hV σ g hg roots
  intro q hq
  let : Fact q.Prime := ⟨hp q hq⟩
  have hsample (u : Fin (2^l)×Fin (2*b)) :
      (ZMod.unitsMap (List.dvd_prod hq) (sourceBulkUnits outside.prod sources (2*b) k l x u):ZMod q)=
        (bulkSamples sources (2*b) k l x u.1 u.2:ZMod q) := by
    change (ZMod.cast (sourceBulkUnits outside.prod sources (2*b) k l x u:ZMod outside.prod):ZMod q)=_
    rw [sourceBulkUnits_coe outside.prod sources (2*b) k l x hcx u,
      ZMod.cast_natCast (List.dvd_prod hq)]
  apply Prod.ext
  · funext path
    exact (rawLeaves_decode_slots sources (2*b) k V l a c x hx _ hsample path).symm
  · funext path
    exact (rawLeaves_decode_slots_permuted b k bulk top comp V l a' c' σ x hx' _ hsample path).symm

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
