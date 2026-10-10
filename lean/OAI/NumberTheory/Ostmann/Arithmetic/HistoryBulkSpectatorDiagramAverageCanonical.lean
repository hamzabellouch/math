import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverageLeaf

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage
open Construction Conclusion CanonicalHistoryLeafBulk HistoryBulkDiagramParameters
open HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorDiagram
variable {q : ℕ} [Fact q.Prime]

theorem canonical_pair_eq_referenceIntegrand
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
    (hf : a0.frequency=a.frequency) (hf' : b0.frequency=a'.frequency)
    (hfix : a0.small.map eraseBulkValue=a.small.map eraseBulkValue)
    (hfix' : b0.small.map eraseBulkValue=a'.small.map eraseBulkValue)
    (hs0 : (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a0 c).Supported V outside)
    (ht0 : (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l b0 c').Supported V outside)
    (hs : (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a c).Supported V outside)
    (ht : (decodeHistory (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l a' c').Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l,V j<q) (g : ZMod q→ℂ) (hg : g 0=0)
    (Xp Xm : (ZMod q)ˣ) :
    let sources := initialSourceFamily b k bulk top comp
    let seed := Template.initial (2*b) k
    let h0 := decodeHistory sources seed V l a0 c
    let k0 := decodeHistory sources seed V l b0 c'
    let h := decodeHistory sources seed V l a c
    let k' := decodeHistory sources seed V l a' c'
    let D := denominatorUnit hs0 hq
    primeSpectator q g D h Xp Xm*conj (primeSpectator q g D k' Xp Xm)=
      orderedIntegrand σ
        (bulkDiagram h0 hs0 (supported_regular h0 hs0 hq hV) D Xp Xm)
        (bulkDiagram k0 ht0 (supported_regular k0 ht0 hq hV) D Xp Xm) g
        (bulkUnits sources (2*b) k V l a c x hx (supported_regular h hs hq hV)) := by
  dsimp only
  rw [primeSpectator_decode_eq_referenceBulkDiagram _ _ V outside l a0 a c hf hfix hs0 hs hq hV g hg,
    primeSpectator_decode_eq_referenceBulkDiagram _ _ V outside l b0 a' c' hf' hfix' ht0 ht hq hV g hg]
  have hp := decodeHistory_leafBulk_pair b k bulk top comp V l a a' c c' σ x hx hx'
    (supported_regular _ hs hq hV) (supported_regular _ ht hq hV)
  exact congrArg (fun z=>
    (bulkDiagram _ hs0 (supported_regular _ hs0 hq hV) (denominatorUnit hs0 hq) Xp Xm).value g z.1*
      conj ((bulkDiagram _ ht0 (supported_regular _ ht0 hq hV) (denominatorUnit hs0 hq) Xp Xm).value g z.2)) hp

end Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage

end

end OAI
