import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverageCanonical

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage
open Construction Conclusion CanonicalHistoryLeafBulk HistoryBulkDiagramParameters
open HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorDiagram
variable {q : ℕ} [Fact q.Prime]

theorem source_pair_eq_referenceIntegrand
    (b k l : ℕ) (bulk : PrimeSource) (top : Fin 3→PrimeSource)
    (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ) (outside : List ℕ)
    (a0 b0 a a' : State)
    (c c' : HistoryChoices (initialSourceFamily b k bulk top comp)
      (Template.initial (2*b) k) V l)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*b)))
    (x0 x : SourceAssignment (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l))
    (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x)
    (hx' : a'.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l)
      (leafBulkAssignmentPermutation b k l bulk top comp σ x))
    (hf : a0.frequency=a.frequency) (hf' : b0.frequency=a'.frequency)
    (hx0 : a0.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x0)
    (hx00 : b0.small=assignedSlots (initialSourceFamily b k bulk top comp)
      (Template.current (Template.initial (2*b) k) l) x0)
    (hfixed : ∀i : Fin (Template.current (Template.initial (2*b) k) l).length,
      (Template.current (Template.initial (2*b) k) l)[i].role≠.bulk →
        (x0 i:ℕ)=(x i:ℕ))
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
  have he := assignedSlots_erase_eq (initialSourceFamily b k bulk top comp)
    (Template.current (Template.initial (2*b) k) l) x0 x hfixed
  have hfix : a0.small.map eraseBulkValue=a.small.map eraseBulkValue := by
    rw [hx0,hx]; exact he
  have hfix' : b0.small.map eraseBulkValue=a'.small.map eraseBulkValue := by
    rw [hx00,hx']
    exact he.trans (assignedSlots_leafBulkPermutation_erase_eq b k l bulk top comp σ x).symm
  exact canonical_pair_eq_referenceIntegrand b k l bulk top comp V outside a0 b0 a a'
    c c' σ x hx hx' hf hf' hfix hfix' hs0 ht0 hs ht hq hV g hg Xp Xm

end Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage

end

end OAI
