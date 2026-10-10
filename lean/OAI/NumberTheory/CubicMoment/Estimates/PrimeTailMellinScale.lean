import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailProductMean

namespace OAI

/-! Eight Mellin moments at B^(1/4) absorb the coarse product mass
throughout A <= B². The remaining factor B^(-1) pays for any fixed log. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primeTail_mellin_error_scale {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B)
    (hAB : A ≤ B^2) :
    A*B/(B^(1/4:ℝ))^8 ≤ A^(5/6:ℝ)*B^(5/6:ℝ)/B := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hVp : 0 < A*B := mul_pos hA hBp
  have hV : A*B ≤ B^3 := by nlinarith [mul_le_mul_of_nonneg_right hAB hBp.le]
  have hroot : (A*B)^(1/6:ℝ) ≤ B := by
    calc
      _ ≤ (B^3)^(1/6:ℝ) := Real.rpow_le_rpow hVp.le hV (by norm_num)
      _ = B^(1/2:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul hBp.le]; norm_num
      _ ≤ B^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
      _ = B := Real.rpow_one B
  have hs : (B^(1/4:ℝ))^8 = B^2 := by
    rw [←Real.rpow_mul_natCast hBp.le]
    norm_num
  rw [hs]
  apply (div_le_div_iff₀ (sq_pos_of_pos hBp) hBp).mpr
  have he : A*B = (A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ) := by
    rw [←Real.rpow_add hVp]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (A*B)^(5/6:ℝ)*B by positivity)
  rw [Real.mul_rpow hA.le hBp.le] at hh
  calc
    A*B*B = ((A*B)^(5/6:ℝ)*(A*B)^(1/6:ℝ))*B := by rw [←he]
    _ = (A^(5/6:ℝ)*B^(5/6:ℝ)*B)*(A*B)^(1/6:ℝ) := by
      rw [Real.mul_rpow hA.le hBp.le]
      ring
    _ ≤ (A^(5/6:ℝ)*B^(5/6:ℝ)*B)*B := hh
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
