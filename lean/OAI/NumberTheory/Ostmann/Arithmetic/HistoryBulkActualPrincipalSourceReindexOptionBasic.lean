import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensationComplete
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPatternSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
local instance optionSourceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}

theorem outerData_left_mass (D : OuterData C p o)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass
      (leftDraws C p D.blockDraw D.valid)≠0 := by
  simpa only [leftChoices,choicesMass_assemble,leftDraws,leftBlockDraws,OuterData.blockDraw,HistoryGiantOriginalMeanFactorization.Seed] using D.left_mass i

theorem outerData_right_mass (D : OuterData C p o)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass
      (rightDraws C p D.blockDraw D.valid)≠0 := by
  simpa only [rightChoices,choicesMass_assemble,rightDraws,rightBlockDraws,OuterData.blockDraw,HistoryGiantOriginalMeanFactorization.Seed] using D.right_mass i

theorem exists_outerData_eq_some (ho : outerMass C l p o≠0)
    (ht : Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q))) :
    ∃D : OuterData C p o,outerData? C p o=some D := by
  have hs := outerData?_isSome_of_mass C p o ho ht
  cases hd : outerData? C p o with
  | none => simp only [hd,Option.isSome_none,Bool.false_eq_true] at hs
  | some D => exact ⟨D,rfl⟩

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
