import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorReplacementSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceDisintegrationSelectedDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateFrequencyConstraint

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreSourceMean
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkPriorGrid
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem unitConvention_bulk_sample (N : ℕ) [NeZero N]
    (hsize : (N : ℝ) < Real.exp (bulkLogLower L)) (p : C.bulk.Sample) :
    Characters.Template.unitConvention (p.val : ZMod N) =
      bulkPrimeUnit L N hsize p.val (bulkPrimeBand_subset_closed L E p.property) := by
  apply Units.ext
  rw [Characters.Template.unitConvention_coe _
    ((ZMod.isUnit_iff_coprime _ _).mpr
      (bulkClosedSupport_coprime L N hsize (bulkPrimeBand_subset_closed L E p.property))),
    bulkPrimeUnit_coe]

theorem selectedBulkPrior_cmean_eq_sourceBulkMean
    (N : ℕ) [NeZero N] (hsize : (N : ℝ) < Real.exp (bulkLogLower L))
    (F : ((Fin (2^l) × Fin (2*(bulkSize k L/2))) → (ZMod N)ˣ) → ℂ)
    (f : ((Fin (2^l) × Fin (2*(bulkSize k L/2))) → ℝ) → ℂ) :
    (selectedBulkPrior C l).cmean (fun u =>
      F (fun i => Characters.Template.unitConvention ((u i).val : ZMod N)) *
        f (fun i => ((u i).val : ℝ))) =
      sourceBulkMean L E C.bulkPositive N hsize F f := by
  rw [sourceBulkMean_selected_eq]
  simp only [unitConvention_bulk_sample C N hsize]
  rfl

end Ostmann.Arithmetic.HistoryBulkFibreSourceMean

end

end OAI
