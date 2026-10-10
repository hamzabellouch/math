import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantGridCellBounds
open PrimeCellActualErrorBudget

theorem correctedPrimeError_antitone_lower {K d lower upper Z : ℝ}
    (hK : 0 ≤ K) (hd : 0 ≤ d) (hZ : 0 < Z)
    (hlower : 0 ≤ lower) (hle : lower ≤ upper) :
    correctedPrimeError K d upper Z ≤ correctedPrimeError K d lower Z := by
  have hpow : lower^(1/3:ℝ) ≤ upper^(1/3:ℝ) :=
    Real.rpow_le_rpow hlower hle (by norm_num)
  have hprime : Real.exp (-d*upper^(1/3:ℝ)) ≤ Real.exp (-d*lower^(1/3:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr hd))
  have hboundary : Real.exp (-upper) ≤ Real.exp (-lower) :=
    Real.exp_le_exp.mpr (neg_le_neg hle)
  unfold correctedPrimeError
  rw [mul_inv_rev,mul_inv_rev,←Real.exp_neg,←Real.exp_neg]
  exact add_le_add (mul_le_mul_of_nonneg_left hprime (div_nonneg hK hZ.le))
    (mul_le_mul_of_nonneg_right hboundary (inv_nonneg.mpr hZ.le))

end Ostmann.Arithmetic.HistoryGiantGridCellBounds

end

end OAI
