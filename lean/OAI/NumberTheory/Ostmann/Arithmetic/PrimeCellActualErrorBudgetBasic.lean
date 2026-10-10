import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementAssigned
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget LogCellPartition Filter

def correctedPrimeError (K d lower Z : ℝ) : ℝ :=
  (K/Z)*Real.exp (-d*lower^(1/3:ℝ))+(Z*Real.exp lower)⁻¹

theorem correctedPrimeError_le {K d c a L lower Z A : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hcd : c ≤ d) (hc1 : c ≤ 1)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hlower : Real.exp (a*L) ≤ lower)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ Real.exp A) :
    correctedPrimeError K d lower Z ≤ (K+1)*Real.exp (A-c*Real.exp ((a/3)*L)) := by
  have hlow1 : 1 ≤ lower := (Real.one_le_exp (mul_nonneg ha hL)).trans hlower
  have hpow : Real.exp ((a/3)*L) ≤ lower^(1/3:ℝ) := by
    have hh := Real.rpow_le_rpow (Real.exp_nonneg (a*L)) hlower (by norm_num : (0:ℝ)≤1/3)
    rw [← Real.exp_mul] at hh
    convert hh using 1
    congr 1
    ring
  have hpowlo : lower^(1/3:ℝ) ≤ lower := Real.rpow_le_self_of_one_le hlow1 (by norm_num)
  have hd : 0 ≤ d := hc.trans hcd
  have hprime : Real.exp (-d*lower^(1/3:ℝ)) ≤ Real.exp (-c*Real.exp ((a/3)*L)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul hcd hpow (Real.exp_nonneg _) hd
    linarith
  have hboundary : Real.exp (-lower) ≤ Real.exp (-c*Real.exp ((a/3)*L)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc1 (Real.exp_nonneg ((a/3)*L))
    linarith [hpow.trans hpowlo]
  unfold correctedPrimeError
  rw [mul_inv_rev,← Real.exp_neg]
  calc
    _ ≤ (K*Real.exp A)*Real.exp (-c*Real.exp ((a/3)*L))+
        Real.exp (-c*Real.exp ((a/3)*L))*Real.exp A := by
      apply add_le_add
      · exact mul_le_mul (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hZi hK)
          hprime (Real.exp_nonneg _) (mul_nonneg hK (Real.exp_nonneg _))
      · exact mul_le_mul hboundary hZi (inv_nonneg.mpr hZ.le) (Real.exp_nonneg _)
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,← neg_mul]; ring

theorem mixedGridIntegerError_le {lo hi η G B D a L : ℝ}
    (j : Fin (gridCount lo hi η)) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hwidth : gridPoint lo hi η (j.val+1)-gridPoint lo hi η j.val ≤ 1)
    (hG : Real.exp (a*L) ≤ G) :
    mixedGridIntegerError lo hi η G B D j ≤ (6*B+2*D)*Real.exp (-Real.exp (a*L)) := by
  unfold mixedGridIntegerError
  have hc : 6*B+2*D*(gridPoint lo hi η (j.val+1)-gridPoint lo hi η j.val) ≤ 6*B+2*D := by
    nlinarith
  calc
    _ ≤ Real.exp (-G)*(6*B+2*D) := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ ≤ Real.exp (-Real.exp (a*L))*(6*B+2*D) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hG)) (by positivity)
    _ = _ := mul_comm _ _

end Ostmann.Arithmetic.PrimeCellActualErrorBudget

end

end OAI
