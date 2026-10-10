import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPriorGridRestoration

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPriorGrid
open Construction PrimeProgression PrimeCellReplacement LogCellPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bulkRealGridMean (L : ℝ) (E : Finset ℕ) (F : (ι → ℕ) → ℝ) : ℝ :=
  ∑ p : BulkPrimeTuple ι L, bulkTupleWeight L E p*F (fun i => (p i).val)

theorem bulkProductPrior_mean_eq_retained_grid (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (F : (ι → ℕ) → ℝ) :
    (bulkProductPrior (ι := ι) L E hZ).mean (fun p => F (fun i => (p i).val)) =
      ∑ p : BulkPrimeTuple ι L, if bulkTupleRetained L E p then
        bulkTupleWeight L E p*F (fun i => (p i).val) else 0 := by
  have he := congrArg Complex.re
    (bulkProductPrior_cmean_eq_retained_grid L E hZ (fun x => (F x : ℂ)))
  simpa [FinitePrior.cmean, FinitePrior.mean, apply_ite] using he

theorem bulkRealGridMean_sub_source_mean_le (L : ℝ) (E : Finset ℕ)
    (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (F : (ι → ℕ) → ℝ)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ p : BulkPrimeTuple ι L, |F (fun i => (p i).val)| ≤ A) :
    |bulkRealGridMean L E F-
      (bulkProductPrior (ι := ι) L E hZ).mean (fun p => F (fun i => (p i).val))| ≤
      (bulkFullMassRatio L E ^ Fintype.card ι-1)*A := by
  have he := bulkGridMean_sub_source_cmean_le L E hZ (fun x => (F x : ℂ)) hA
    (fun p => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hF p)
  simpa only [bulkGridMean, bulkRealGridMean, FinitePrior.cmean, FinitePrior.mean,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using he

end Ostmann.Arithmetic.HistoryBulkPriorGrid

end

end OAI
