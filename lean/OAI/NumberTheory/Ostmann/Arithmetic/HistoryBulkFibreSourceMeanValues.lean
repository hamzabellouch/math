import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreSourceMean
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference CanonicalHistoryLeafBulk
open HistoryBulkReferenceScalarCoordinates
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

@[simp] theorem bulkSamples_fibreAssignment (a : SelectedNonbulkSample C l)
    (u : SelectedBulkSample C l) (b : Fin (2^l)) (i : Fin (2*(bulkSize k L/2))) :
    bulkSamples C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u) b i =
      (u (b,i)).val := by
  have hv := selectedSourceEquiv_bulk_val C l (fibreAssignment C a u) (b,i)
  simpa only [fibreAssignment, Equiv.apply_symm_apply, bulkSamples] using hv.symm

@[simp] theorem orderedSourceValues_fibreAssignment (a : SelectedNonbulkSample C l)
    (u : SelectedBulkSample C l) :
    orderedSourceValues C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u) =
      fun j => ((u j).val : ℝ) := by
  funext j
  change (bulkSamples C.sources (2*(bulkSize k L/2)) k l
    (fibreAssignment C a u) j.1 j.2 : ℝ) = ((u j).val : ℝ)
  rw [bulkSamples_fibreAssignment]

end Ostmann.Arithmetic.HistoryBulkFibreSourceMean

end

end OAI
