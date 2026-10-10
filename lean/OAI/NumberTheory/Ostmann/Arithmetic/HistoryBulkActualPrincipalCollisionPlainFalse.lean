import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionFalseMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainFalseDefs

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

theorem plainCollisionMean_false_eq_plainBulkPattern (bg : Background C l) :
    plainCollisionMean C spectator ds hactual hl σ mixed hV bg false =
      plainBulkPattern C spectator ds hactual hl σ mixed hV bg := by
  cases mixed with
  | false =>
    exact @selectedCollisionMean_false_eq_pattern d Bs BD Bz L k l E C
      (spectatorList spectator ds) σ
      (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
      (PrimeDraw C.giant) inferInstance (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      spectator hactual hl (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV bg false false
  | true =>
    exact @selectedCollisionMean_false_eq_pattern d Bs BD Bz L k l E C
      (spectatorList spectator ds) σ
      (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))=>
        plainMixedWeight C (spectatorList spectator ds) bg.2 i.1.val)
      (MixedDraw C.giantCenter C.giant) inferInstance
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
      spectator hactual hl (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV bg false true

theorem plainCollisionPrincipal_false_eq_plainBulkPrincipal :
    plainCollisionPrincipal C spectator ds hactual hl σ mixed hV false =
      plainBulkPrincipal C spectator ds hactual hl σ mixed hV :=
  (FinitePrior.cmean_congr_support (backgroundPrior C l) _ _
    (fun bg _=>plainCollisionMean_false_eq_plainBulkPattern C spectator ds hactual hl σ mixed hV bg)).trans
    (plainBulkPrincipal_eq_background_pattern C spectator ds hactual hl σ mixed hV).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
