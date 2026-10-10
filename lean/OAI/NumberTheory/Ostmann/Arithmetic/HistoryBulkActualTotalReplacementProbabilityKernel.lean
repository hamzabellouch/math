import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementSquareDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalSourceReindexFamily
open HistoryBulkFibreGiantApproximationReference HistoryGiantReferenceMean
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (D : PlainStageData C spectator l) (hl : l≤k)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))

theorem plainSquareValue_probability_eq_kernel
    (mixed : Bool) (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) :
    plainSquareValue C spectator D hl σ mixed true ds =
      plainKernelValue C spectator D hl σ mixed false ds := by
  cases mixed with
  | false =>
    exact background_probability_rootExpression_eq_kernel_sum C (spectatorList spectator ds) σ
      (primeLawMultiplier C) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      D.reference hl
      (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
      (primeWeight_nonneg C.giant) (fun r _ => primeDraw_positive C.giant r)
      (fun r hr => prime_draw_cells C r
        (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      (D.admissible ds) List.length_ofFn (D.residues ds) false false
  | true =>
    exact background_probability_rootExpression_eq_kernel_sum C (spectatorList spectator ds) σ
      (plainMixedLawMultiplier C (spectatorList spectator ds))
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
      (mixedQ C.giantCenter C.giant) D.reference hl
      (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
      (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr => mixed_draw_cells C r
        (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      (D.admissible ds) List.length_ofFn (D.residues ds) false true

theorem plainSquareAverage_probability_eq_kernel (mixed : Bool) :
    plainSquareAverage C spectator D hl σ mixed true =
      plainKernelAverage C spectator D hl σ mixed false := by
  unfold plainSquareAverage plainKernelAverage
  apply congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
  funext ds
  exact plainSquareValue_probability_eq_kernel C spectator D hl σ mixed ds

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
