import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrame
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkSelectedPrincipalAmplitude HistoryBulkGiantCorrectedBounds
open HistoryPairGiantCoordinates HistoryBulkGoodPatternPrincipalFrame
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem giantValue_eq_giantScalar
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
    (r : Frame (l:=l) C outside) (a : SelectedNonbulkSample C l)
    (u : SelectedBulkSample C l) (corrected mixed : Bool) :
    giantValue r corrected mixed (fibreAssignment C a u) =
      if corrected then
        if mixed then mixedGiantScalar C.giantCenter (logCellMass C.giantCenter ∅)
          (jointCorrectedScalar C (bulkSize k L/2) r.left r.right r.left_supported
            r.right_supported (optionEquiv r.left r.right) (orderedBulkEquiv r))
          (fun j=>((u j).val:ℝ))
        else primeGiantScalar C.giantCenter (logCellMass C.giantCenter ∅)
          (jointCorrectedScalar C (bulkSize k L/2) r.left r.right r.left_supported
            r.right_supported (boolEquiv r.left r.right) (orderedBulkEquiv r))
          (fun j=>((u j).val:ℝ))
      else
        if mixed then mixedGiantScalar C.giantCenter (logCellMass C.giantCenter ∅)
          (jointScalar C (bulkSize k L/2) r.left r.right r.left_supported
            r.right_supported (optionEquiv r.left r.right) (orderedBulkEquiv r))
          (fun j=>((u j).val:ℝ))
        else primeGiantScalar C.giantCenter (logCellMass C.giantCenter ∅)
          (jointScalar C (bulkSize k L/2) r.left r.right r.left_supported
            r.right_supported (boolEquiv r.left r.right) (orderedBulkEquiv r))
          (fun j=>((u j).val:ℝ)) := by
  have hm : r.mixedScalar (fibreAssignment C a u) = fun v =>
      jointScalar C (bulkSize k L/2) r.left r.right r.left_supported r.right_supported
        (optionEquiv r.left r.right) (orderedBulkEquiv r) v (fun j=>((u j).val:ℝ)) := by
    unfold Frame.mixedScalar
    rw [orderedSourceValues_fibreAssignment]
    rfl
  have hc : r.correctedMixedScalar (fibreAssignment C a u) = fun v =>
      jointCorrectedScalar C (bulkSize k L/2) r.left r.right r.left_supported r.right_supported
        (optionEquiv r.left r.right) (orderedBulkEquiv r) v (fun j=>((u j).val:ℝ)) := by
    unfold Frame.correctedMixedScalar
    rw [orderedSourceValues_fibreAssignment]
    rfl
  cases corrected <;> cases mixed <;>
    simp only [giantValue, Bool.false_eq_true, ↓reduceIte, Frame.mixedIntegralValue,
      hm, hc, primeGiantScalar, mixedGiantScalar,
      HistoryBulkGiantCorrectedBounds.primeJointCutoff,
      HistoryBulkGiantCorrectedBounds.mixedJointCutoff,
      orderedSourceValues_fibreAssignment]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrame

end

end OAI
