import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityTail

namespace OAI

/-! A quantitative witness radius for the ordinary density selection. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def densityRadiusConstant : ℝ := max 1 (2*(∫ z, topProfile 3 z ∂volume.prod volume))

def densityRadius (eta : ℝ) : ℝ :=
  densityRadiusConstant * max 1 (eta^(-(1/100:ℝ)))

theorem densityRadiusConstant_ge_one : 1 ≤ densityRadiusConstant := le_max_left _ _

theorem densityRadius_ge_one (eta : ℝ) : 1 ≤ densityRadius eta := by
  have h := densityRadiusConstant_ge_one
  have hm : (1:ℝ)≤max 1 (eta^(-(1/100:ℝ))) := le_max_left _ _
  dsimp only [densityRadius]
  nlinarith

theorem densityRadius_le (eta : ℝ) (heta : 0≤eta) :
    densityRadius eta ≤ densityRadiusConstant*(1+eta^(-(1/100:ℝ))) := by
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans densityRadiusConstant_ge_one)
  exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg heta _))
    (le_add_of_nonneg_left zero_le_one)

theorem densityRadius_tail {eta : ℝ} (heta : 0<eta) :
    (densityRadius eta)^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2 := by
  let C := ∫ z, topProfile 3 z ∂volume.prod volume
  let A := densityRadiusConstant
  let x := max 1 (eta^(-(1/100:ℝ)))
  have hC : 0≤C := integral_nonneg (topProfile_nonnegative 3)
  have hA : 1≤A := densityRadiusConstant_ge_one
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hCA : 2*C≤A := le_max_right _ _
  have hx : 1≤x := le_max_left _ _
  have hxp : 0<x := zero_lt_one.trans_le hx
  have hhalf : A^(-(200:ℝ))*C≤1/2 := by
    calc
      _ ≤ A^(-(1:ℝ))*C := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hA (by norm_num)) hC
      _ = C/A := by rw [Real.rpow_neg_one]; ring
      _ ≤ 1/2 := (div_le_iff₀ hAp).mpr (by linarith)
  have hxsmall : x^(-(200:ℝ))≤eta := by
    by_cases he : eta≤1
    · have hbase : eta^(-(1/100:ℝ))≤x := le_max_right _ _
      have hp := Real.rpow_le_rpow_of_nonpos
        (Real.rpow_pos_of_pos heta (-(1/100:ℝ))) hbase (by norm_num : -(200:ℝ)≤0)
      have hid : (eta^(-(1/100:ℝ)))^(-(200:ℝ))=eta^2 := by
        rw [←Real.rpow_mul heta.le]
        norm_num
      rw [hid] at hp
      exact hp.trans (by nlinarith)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)).trans (le_of_not_ge he)
  change (A*x)^(3-(203:ℝ))*C≤eta/2
  norm_num only [show (3-(203:ℝ))= -200 by norm_num]
  rw [Real.mul_rpow hAp.le hxp.le]
  calc
    A^(-(200:ℝ))*x^(-(200:ℝ))*C = (A^(-(200:ℝ))*C)*x^(-(200:ℝ)) := by ring
    _ ≤ (1/2)*x^(-(200:ℝ)) :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hxp.le _)
    _ ≤ (1/2)*eta := mul_le_mul_of_nonneg_left hxsmall (by norm_num)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
