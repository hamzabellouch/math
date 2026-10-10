import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionSelectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkActualPrincipalBlockFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximationReference
open HistoryGiantReferenceMean HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainKernelCollisionSourceValue (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample)
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (hl : l≤k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  (backgroundPrior C l).cmean (fun bg=>
    if mixed then
      selectedCollisionMean (α:=MixedDraw C.giantCenter C.giant) (spectator:=spectator)
        C (spectatorList spectator ds) σ
        (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
          (u : SelectedBulkSample C l) (P Q : ℤ)=>
          (HistoryDiagonalSmallOriginalMean.smallMultiplier C (spectatorList spectator ds)
            (fibreAssignment C bg.2 u) i.1.val P Q : ℂ))
        (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
        hactual hl (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩)) (mixedWeight_nonneg C.giantCenter C.giant)
        (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
        (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
        List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        hV bg false true true
    else
      selectedCollisionMean (α:=PrimeDraw C.giant) (spectator:=spectator)
        C (spectatorList spectator ds) σ
        (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
        (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
        hactual hl (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩)) (primeWeight_nonneg C.giant)
        (fun r _=>primeDraw_positive C.giant r)
        (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
        List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
        hV bg false false true)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
