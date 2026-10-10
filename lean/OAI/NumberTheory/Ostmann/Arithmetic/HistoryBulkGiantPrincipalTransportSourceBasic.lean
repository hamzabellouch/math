import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction Conclusion ScaleBudget PrimeCellActualErrorBudget
open HistoryBulkReferenceGiantDerivative HistorySelectedPairDerivativeBounds

lemma cutoff_exp_le_smoothGrowth (Bs BD Bz L : ℝ) (k₀ : ℕ) :
    Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) ≤
      smoothGrowthFactor k₀ (cutoffExponent Bs BD Bz k₀) giant.μ L := by
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg (cutoffExponent_pos Bs BD Bz k₀).le
    (show 0≤(bulkSize k₀ L:ℝ)+1 by positivity)) (Real.exp_nonneg (giant.μ*L))]

lemma selected_exp_le_cutoff_smoothGrowth (Bs BD Bz L : ℝ) (k₀ : ℕ) :
    Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) ≤
      smoothGrowthFactor k₀ (cutoffExponent Bs BD Bz k₀) giant.μ L :=
  (exp_le_cutoff_exp (selectedExponent Bs BD Bz k₀) (bulkSize k₀ L)).trans
    (cutoff_exp_le_smoothGrowth Bs BD Bz L k₀)

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
