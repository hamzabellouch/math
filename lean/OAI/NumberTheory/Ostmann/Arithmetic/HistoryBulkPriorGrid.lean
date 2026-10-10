import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridReal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement LogCellPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selected_bulk_cmean_eq_retained_grid
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (F : (ι → ℕ) → ℂ) :
    (dependentProductPrior (fun _ : ι => C.bulk.law)).cmean
      (fun p => F (fun i => (p i).val)) =
      ∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then
        (bulkTupleWeight L E p : ℂ)*F (fun i => (p i).val) else 0 :=
  bulkProductPrior_cmean_eq_retained_grid L E C.bulkPositive F

theorem selected_bulk_grid_restoration_le
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (F : (ι → ℕ) → ℂ)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ p : BulkPrimeTuple ι L, ‖F (fun i => (p i).val)‖ ≤ A) :
    ‖bulkGridMean L E F-(dependentProductPrior (fun _ : ι => C.bulk.law)).cmean
      (fun p => F (fun i => (p i).val))‖ ≤
      ((1+3*Real.exp (-bulkLogLower L)/bulkNormalizer L E)^Fintype.card ι-1)*A := by
  apply (bulkGridMean_sub_source_cmean_le L E C.bulkPositive F hA hF).trans
  apply mul_le_mul_of_nonneg_right _ hA
  apply sub_le_sub_right
  apply pow_le_pow_left₀ ((bulkFullMassRatio_bounds L E C.bulkPositive).1.trans' zero_le_one)
  exact (bulkFullMassRatio_bounds L E C.bulkPositive).2.trans
    (add_le_add le_rfl (bulkRestorationCap_le_three L E C.bulkPositive C.deleted_card))

theorem selected_ordered_bulk_grid_restoration_le
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (m l : ℕ)
    (F : ((Fin (2^l) × Fin m) → ℕ) → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ p : BulkPrimeTuple (Fin (2^l) × Fin m) L,
      ‖F (fun i => (p i).val)‖ ≤ A) :
    ‖bulkGridMean L E F-(dependentProductPrior
      (fun _ : Fin (2^l) × Fin m => C.bulk.law)).cmean
      (fun p => F (fun i => (p i).val))‖ ≤
      ((1+3*Real.exp (-bulkLogLower L)/bulkNormalizer L E)^(2^l*m)-1)*A := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    selected_bulk_grid_restoration_le C F hA hF

theorem selected_bulk_real_grid_restoration_le
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (F : (ι → ℕ) → ℝ)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ p : BulkPrimeTuple ι L, |F (fun i => (p i).val)| ≤ A) :
    |bulkRealGridMean L E F-(dependentProductPrior (fun _ : ι => C.bulk.law)).mean
      (fun p => F (fun i => (p i).val))| ≤
      (bulkFullMassRatio L E^Fintype.card ι-1)*A :=
  bulkRealGridMean_sub_source_mean_le L E C.bulkPositive F hA hF

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
