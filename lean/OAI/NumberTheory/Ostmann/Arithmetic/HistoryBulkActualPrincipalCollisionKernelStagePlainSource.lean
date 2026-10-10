import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainCollisionDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainLaw

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator) (hl : l≤k)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))

theorem plainKernelSourceValue_eq_collisionSourceValue (mixed : Bool)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    plainKernelSourceValue C spectator hactual hl σ mixed ds hV =
      plainKernelCollisionSourceValue C spectator ds hactual hl σ mixed hV := by
  cases mixed with
  | false =>
    unfold plainKernelSourceValue plainKernelCollisionSourceValue
    exact @sum_selectedKernelMean_eq_collisionPrincipal d Bs BD Bz L k l E C
      (spectatorList spectator ds) σ (HistoryBulkActualBSquareReplacement.primeLawMultiplier C)
      (HistoryGiantReferenceMean.PrimeDraw C.giant) inferInstance
      (HistoryGiantReferenceMean.primeWeight C.giant) (HistoryGiantReferenceMean.primeP C.giant)
      (HistoryGiantReferenceMean.primeQ C.giant) spectator hactual hl
      (fun _q hq => (List.mem_ofFn.mp hq).elim (fun index hindex => ⟨ds index,hindex⟩))
      (HistoryGiantReferenceMean.primeWeight_nonneg C.giant)
      (fun reference _ => HistoryGiantReferenceMean.primeDraw_positive C.giant reference)
      (fun reference hreference => HistoryBulkFibreGiantApproximationReference.prime_draw_cells C reference
        (lt_of_le_of_ne (HistoryGiantReferenceMean.primeWeight_nonneg C.giant reference) (Ne.symm hreference)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV false false
  | true =>
    unfold plainKernelSourceValue plainKernelCollisionSourceValue
    exact @sum_selectedKernelMean_eq_collisionPrincipal d Bs BD Bz L k l E C
      (spectatorList spectator ds) σ
      (HistoryBulkActualBSquareReplacement.plainMixedLawMultiplier C (spectatorList spectator ds))
      (HistoryGiantReferenceMean.MixedDraw C.giantCenter C.giant) inferInstance
      (HistoryGiantReferenceMean.mixedWeight C.giantCenter C.giant)
      (HistoryGiantReferenceMean.mixedP C.giantCenter C.giant)
      (HistoryGiantReferenceMean.mixedQ C.giantCenter C.giant) spectator hactual hl
      (fun _q hq => (List.mem_ofFn.mp hq).elim (fun index hindex => ⟨ds index,hindex⟩))
      (HistoryGiantReferenceMean.mixedWeight_nonneg C.giantCenter C.giant)
      (fun reference _ => HistoryGiantReferenceMean.mixedDraw_positive C.giantCenter C.giant reference)
      (fun reference hreference => HistoryBulkFibreGiantApproximationReference.mixed_draw_cells C reference
        (lt_of_le_of_ne (HistoryGiantReferenceMean.mixedWeight_nonneg C.giantCenter C.giant reference)
          (Ne.symm hreference)))
      List.length_ofFn (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      hV false true

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
