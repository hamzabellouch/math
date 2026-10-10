import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexFrequency

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryBulkUniversalPatternAggregation HistoryBulkSelectedUniversalOperator
open HistoryBulkPrincipalSourceReindex
attribute [local instance] Classical.propDecidable
local instance universalPrincipalReplacementFamilyInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}

def replacementRootFamily (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (j : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    Option (HistoryBulkPatternIntegralReplacement.Reference C outside l p) :=
  if hi : (family.refs j).isSome then some (replacementReference family hp ⟨j,hi⟩) else none

def replacementFamily (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) : HistoryBulkPatternIntegralReplacement.Family C outside l p :=
  extendCommonRootOption (frequencyBound Bs BD Bz k L) l (replacementRootFamily family hp)

theorem familyValue_replacementFamily
    (family : SymbolicPatternFamily C outside l p)
    (hp : ∀q∈outside,q.Prime) (hσ : family.permutation=Equiv.refl _)
    (mixed : Bool)
    (hm : ∀i,family.mask i=assignmentDensity (family.data i).assignment mixed)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    HistoryBulkPatternIntegralReplacement.familyValue true (replacementFamily family hp)
      b false mixed hV = family.value b mixed (bulkSize k L/2) hp hV := by
  unfold HistoryBulkPatternIntegralReplacement.familyValue replacementFamily
  rw [sum_extendCommonRootOption]
  unfold SymbolicPatternFamily.value
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (family.refs j).isSome
  · simp only [replacementRootFamily,dite_eq_left hj,Option.elim_some,
      ite_true,presentComplexValue]
    exact replacementReference_term family hp ⟨j,hj⟩ hσ mixed (hm _) b hV
  · simp only [replacementRootFamily,dite_eq_right hj,Option.elim_none,
      presentComplexValue]

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
