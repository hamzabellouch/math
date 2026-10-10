import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

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
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (mixed : Bool)
  (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def plainCollisionMean (bg : Background C l) (guarded : Bool) : ℂ :=
  if mixed then
    selectedCollisionMean (α:=MixedDraw C.giantCenter C.giant) (spectator:=spectator)
      C (spectatorList spectator ds) σ
      (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))=>
        plainMixedWeight C (spectatorList spectator ds) bg.2 i.1.val)
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
      hactual hl (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV bg false true guarded
  else
    selectedCollisionMean (α:=PrimeDraw C.giant) (spectator:=spectator)
      C (spectatorList spectator ds) σ
      (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV bg false false guarded

def plainCollisionPrincipal (guarded : Bool) : ℂ :=
  (backgroundPrior C l).cmean (fun bg=>plainCollisionMean C spectator ds hactual hl σ mixed hV bg guarded)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
