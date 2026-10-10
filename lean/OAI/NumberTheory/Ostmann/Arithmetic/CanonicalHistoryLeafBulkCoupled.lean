import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkHaar
import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkUnits

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk
open Construction Conclusion HistoryResidueRegular

variable {q : ℕ} [Fact q.Prime]
variable (b k : ℕ) (bulk : PrimeSource)
  (top : Fin 3→PrimeSource) (comp : Fin k→Fin 2→PrimeSource) (V : ℕ→ℕ)
  (l : ℕ) (a a' : State)
  (c c' : HistoryChoices (initialSourceFamily b k bulk top comp) (Template.initial (2*b) k) V l)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*b)))
  (x : SourceAssignment (initialSourceFamily b k bulk top comp)
    (Template.current (Template.initial (2*b) k) l))
  (hx : a.small=assignedSlots (initialSourceFamily b k bulk top comp)
    (Template.current (Template.initial (2*b) k) l) x)
  (hx' : a'.small=assignedSlots (initialSourceFamily b k bulk top comp)
    (Template.current (Template.initial (2*b) k) l)
    (leafBulkAssignmentPermutation b k l bulk top comp σ x))
  (hr : Regular q (decodeHistory (initialSourceFamily b k bulk top comp)
    (Template.initial (2*b) k) V l a c))
  (hr' : Regular q (decodeHistory (initialSourceFamily b k bulk top comp)
    (Template.initial (2*b) k) V l a' c'))

include hx hx'

theorem decodeHistory_leafBulk_pair :
    (HistoryTreeParameters.leafBulk _ hr,HistoryTreeParameters.leafBulk _ hr')=
      orderedProducts σ (bulkUnits (initialSourceFamily b k bulk top comp)
        (2*b) k V l a c x hx hr) := by
  apply Prod.ext
  · funext path
    exact decodeHistory_leafBulk (initialSourceFamily b k bulk top comp)
      (2*b) k V l a c x hx hr path
  · funext path
    exact decodeHistory_leafBulk_permuted b k bulk top comp V l a a' c c' σ x hx hx' hr hr' path

theorem decodeHistory_leafBulk_pair_eq_slotLeaves :
    (HistoryTreeParameters.leafBulk _ hr,HistoryTreeParameters.leafBulk _ hr')=
      PermutationDiagramComparison.slotLeaves (haarPermutation σ)
        (haarSamples (bulkUnits (initialSourceFamily b k bulk top comp)
          (2*b) k V l a c x hx hr)) :=
  (decodeHistory_leafBulk_pair b k bulk top comp V l a a' c c' σ x hx hx' hr hr').trans
    (orderedProducts_eq_slotLeaves σ _)

theorem decodeHistory_leafBulk_pair_eq_coupled (hm : 0<2*b) :
    (HistoryTreeParameters.leafBulk _ hr,HistoryTreeParameters.leafBulk _ hr')=
      (TreePermutationHaar.coupledEquiv (haarPermutation σ) hm
        (PermutationHaar.toCoupled (haarPermutation σ) hm
          (haarSamples (bulkUnits (initialSourceFamily b k bulk top comp)
            (2*b) k V l a c x hx hr)))).val := by
  exact (decodeHistory_leafBulk_pair b k bulk top comp V l a a' c c' σ x hx hx' hr hr').trans
    (orderedProducts_eq_leafPairEquiv σ _)

theorem decodeHistory_leafBulk_pair_coupled (hm : 0<2*b) :
    (TreePermutationHaar.leftPartition (haarPermutation σ)).coupled
      (TreePermutationHaar.rightPartition (haarPermutation σ) hm)
      (HistoryTreeParameters.leafBulk _ hr,HistoryTreeParameters.leafBulk _ hr') := by
  rw [decodeHistory_leafBulk_pair b k bulk top comp V l a a' c c' σ x hx hx' hr hr']
  exact orderedProducts_coupled σ hm _

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
