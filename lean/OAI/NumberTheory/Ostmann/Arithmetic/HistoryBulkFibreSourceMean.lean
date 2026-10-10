import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreSourceMeanBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreSourceMeanValues
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreSourceMean
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkPriorGrid
open HistoryBulkFibreOriginalReference HistoryBulkReferenceScalarCoordinates
open HistoryBulkSpectatorReferenceRaw
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem sourceBulkUnits_fibreAssignment (a : SelectedNonbulkSample C l)
    (u : SelectedBulkSample C l) (N : ℕ) :
    sourceBulkUnits N C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u) =
      fun i => Characters.Template.unitConvention ((u i).val : ZMod N) := by
  funext i
  simp only [sourceBulkUnits, bulkSamples_fibreAssignment]

theorem sourceBulkUnits_fibreAssignment_eq_bulkTupleUnits
    (a : SelectedNonbulkSample C l) (u : SelectedBulkSample C l)
    (N : ℕ) [NeZero N] (hsize : (N : ℝ) < Real.exp (bulkLogLower L)) :
    sourceBulkUnits N C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u) =
      bulkTupleUnits L N hsize
        (fun i => ⟨(u i).val, bulkPrimeBand_subset_closed L E (u i).property⟩) := by
  rw [sourceBulkUnits_fibreAssignment]
  funext i
  exact unitConvention_bulk_sample C N hsize (u i)

theorem fibre_cmean_eq_sourceBulkMean (a : SelectedNonbulkSample C l)
    (N : ℕ) [NeZero N] (hsize : (N : ℝ) < Real.exp (bulkLogLower L))
    (F : ((Fin (2^l) × Fin (2*(bulkSize k L/2))) → (ZMod N)ˣ) → ℂ)
    (f : ((Fin (2^l) × Fin (2*(bulkSize k L/2))) → ℝ) → ℂ) :
    (selectedBulkPrior C l).cmean (fun u =>
      F (sourceBulkUnits N C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u)) *
        f (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u))) =
      sourceBulkMean L E C.bulkPositive N hsize F f := by
  simp only [sourceBulkUnits_fibreAssignment, orderedSourceValues_fibreAssignment]
  exact selectedBulkPrior_cmean_eq_sourceBulkMean C N hsize F f

theorem fibre_cmean_integrated_eq_sourceBulkMean (a : SelectedNonbulkSample C l)
    (N : ℕ) [NeZero N] (hsize : (N : ℝ) < Real.exp (bulkLogLower L))
    (F : ((Fin (2^l) × Fin (2*(bulkSize k L/2))) → (ZMod N)ˣ) → ℂ)
    {Θ : Type*} (I : (Θ → ℂ) → ℂ)
    (f : Θ → ((Fin (2^l) × Fin (2*(bulkSize k L/2))) → ℝ) → ℂ) :
    (selectedBulkPrior C l).cmean (fun u =>
      F (sourceBulkUnits N C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u)) *
        I (fun q => f q
          (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l (fibreAssignment C a u)))) =
      sourceBulkMean L E C.bulkPositive N hsize F (fun x => I (fun q => f q x)) :=
  fibre_cmean_eq_sourceBulkMean C a N hsize F (fun x => I (fun q => f q x))

end Ostmann.Arithmetic.HistoryBulkFibreSourceMean

end

end OAI
