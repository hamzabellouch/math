import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkActualPrincipalBlockFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreGiantApproximation HistoryGiantReferenceMean
open HistoryBulkFibreGiantErrorAverage HistoryBulkFibreOriginalReference
open HistoryBulkActualGoodPrincipal HistoryBulkPatternIntegralReplacement
open HistoryBulkUniversalPatternAggregation HistoryBulkActualIntegralReplacement
attribute [local instance] Classical.propDecidable
attribute [local instance] HistoryBulkPatternIntegralReplacement.bulkBackgroundInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (mixed : Bool)
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def plainBulkPattern (bg : Background C l) : ℂ :=
  patternComplexSum C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    (fun p b=>familyValue (C:=C) (outside:=spectatorList spectator ds) (l:=l) (p:=p) false
      (plainPatternFamily C spectator ds hactual hl σ mixed p (restoreOuterBackground C l p bg b))
      b false mixed hV)

theorem plainBulkPrincipal_eq_background_pattern :
    plainBulkPrincipal C spectator ds hactual hl σ mixed hV =
      (backgroundPrior C l).cmean (plainBulkPattern C spectator ds hactual hl σ mixed hV) := rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
