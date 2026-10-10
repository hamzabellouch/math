import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexWitnessBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkPrincipalSourceReindex HistoryBulkUniversalPatternAggregation
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)

def drawPatternValue
    (F : (Fin (2*(bulkSize k L/2))→spectator.Sample) → SelectedNonbulkSample C l →
      Draws C (l:=l) → Draws C (l:=l) → RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → ℂ)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) (a : SelectedNonbulkSample C l)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  sourcePatternValue C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    (fun z=>F ds a (fun j=>z (Sum.inl j)) (fun j=>z (Sum.inr j)) i) p b

theorem internal_cmean_pair
    (F : Draws C (l:=l) → Draws C (l:=l) → ℂ) :
    (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean (fun x=>
      (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean (fun y=>F x y)) =
    (pairedInternalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean
      (fun z=>F (fun j=>z (Sum.inl j)) (fun j=>z (Sum.inr j))) := by
  simpa only [FinitePrior.cmean,Finset.mul_sum,mul_assoc] using
    (sum_pairedInternalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l F).symm

theorem drawPatternValue_of_valid
    (F : (Fin (2*(bulkSize k L/2))→spectator.Sample) → SelectedNonbulkSample C l →
      Draws C (l:=l) → Draws C (l:=l) → RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → ℂ)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) (a : SelectedNonbulkSample C l)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
    (hb : ∀j,(expand p b j).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates) :
    drawPatternValue C spectator F ds a i p b.val =
      F ds a (leftDraws C p b hb) (rightDraws C p b hb) i / blockJacobian C p b := by
  have he : extendSourceTest C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun z=>F ds a (fun j=>z (Sum.inl j)) (fun j=>z (Sum.inr j)) i) (expand p b) =
      F ds a (leftDraws C p b hb) (rightDraws C p b hb) i :=
    dite_eq_left hb
  exact congrArg (fun z : ℂ=>z/blockJacobian C p b) he

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern

end

end OAI
