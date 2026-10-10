import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalRootTestMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsFrequencySource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalRootTest
open Construction Conclusion CanonicalHistoryLeafBulk HistoryBulkProducts HistoryBulkDiagramParameters
open HistoryBulkSupportConverse HistoryBulkFrequencyTransport HistorySignedSpectatorCRT
open HistoryBulkSpectatorProduct HistoryCRTIntegration HistoryBulkSpectatorReferenceRaw
open HistoryBulkSelectedIntegralReplacement HistoryBulkResidueNormSum HistoryFrequencyResidues ResidueHaar

theorem independent_mixed_source_eq_raw_product_of_mass (d : Decomposition) (K : ℕ)
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
    (hmass : (assignmentPrior (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)).mass x≠0)
    (hfreq : ∀j≤l,∀origin,((initialSourceFamily b k bulk top comp) origin).AboveFrequency (V j)) :
    let H := (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a0 c)
    let G := (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l b0 c')
    letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
    letI : NeZero (pairedFrequencyProduct H G) := ⟨pairedFrequencyProduct_ne_zero hs0 ht0⟩
    rootTest true true d H G hs0 ht0 hp hV σ K
      (sourceBulkUnits (outside.prod*(pairedFrequencyProduct H G)^(K+2))
        (initialSourceFamily b k bulk top comp) (2*b) k l x)=
      average (fun roots : MixedPair outside.prod=>
        residuePairSpectator (residueTransform d) outside outside.prod
          (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a c)
          (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a' c')
          (roots.1,roots.2))*
      average (fun roots : MixedPair ((pairedFrequencyProduct H G)^(K+2))=>
        independentRTest K H G σ ((roots.1:ZMod ((pairedFrequencyProduct H G)^(K+2))),
          (roots.2:ZMod ((pairedFrequencyProduct H G)^(K+2))))
          (sourceBulkUnits ((pairedFrequencyProduct H G)^(K+2))
            (initialSourceFamily b k bulk top comp) (2*b) k l x)) := by
  apply independent_mixed_source_eq_raw_product d K b k l bulk top comp V outside
    a0 b0 a a' c c' σ x y hx hx' hbulk ha0 hb0 hf hf' hfix hfix' hs0 ht0 hc hc' hp hV
  apply Nat.coprime_mul_iff_right.mpr
  refine ⟨hc,?_⟩
  rw [hx]
  exact HistoryBulkReferenceTestsFrequency.source_bulk_coprime_frequency_power
    (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l a0 c) (decodeHistory (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l b0 c') hs0 ht0 hfreq _ x hmass (K+2)

end Ostmann.Arithmetic.HistoryBulkPrincipalRootTest

end

end OAI
