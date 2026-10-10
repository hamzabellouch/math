import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTreeDerivBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Characters.RationalHistory
open scoped FourierTransform SchwartzMap

def partitionDerivativeConstant : ℝ := Classical.choose smoothPartition_deriv_uniform

theorem partitionDerivativeConstant_pos : 0 < partitionDerivativeConstant :=
  (Classical.choose_spec smoothPartition_deriv_uniform).1

theorem partition_deriv_le_constant (z : ℝ) : |deriv smoothPartition z| ≤ partitionDerivativeConstant :=
  (Classical.choose_spec smoothPartition_deriv_uniform).2 z

def cellDerivativeConstant : ℝ := Classical.choose giantCell_logCurve_deriv_bound

theorem cellDerivativeConstant_pos : 0 < cellDerivativeConstant :=
  (Classical.choose_spec giantCell_logCurve_deriv_bound).1

theorem cell_deriv_le_constant {ι : Type} [DecidableEq ι]
    (e : Expr ι) (x : ι → ℝ) (i : ι) (G K : ℝ)
    (hK : 1 ≤ K) (he : e.RelativeControl x K) :
    |deriv (fun t => giantCell G (e.realEval (Expr.logCurve x i t))) 0| ≤
      cellDerivativeConstant * e.logBudget K :=
  (Classical.choose_spec giantCell_logCurve_deriv_bound).2 e x i G K hK he

namespace HistorySymbolicEncoding

def actualSourceDerivativeRate (B : ℝ) : ℝ :=
  sourceDerivativeRate B partitionDerivativeConstant cellDerivativeConstant

theorem actualSourceDerivativeRate_nonneg {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ actualSourceDerivativeRate B := sourceDerivativeRate_nonneg hB
      partitionDerivativeConstant_pos.le cellDerivativeConstant_pos.le

theorem cellDerivativeConstant_mul_le_rate {B : ℝ} (hB : 0 ≤ B) :
    cellDerivativeConstant * B ≤ actualSourceDerivativeRate B := by
  unfold actualSourceDerivativeRate sourceDerivativeRate
  have hp := (leafProfileBound_pos (𝓕 SchwartzCutoff.psi)).le
  have hd := partitionDerivativeConstant_pos.le
  nlinarith [mul_nonneg hB hp,mul_nonneg hB hd]

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
