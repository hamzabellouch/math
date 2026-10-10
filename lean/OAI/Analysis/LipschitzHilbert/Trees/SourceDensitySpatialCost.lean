import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityRadius

namespace OAI

/-! The number of translated ordinary trees in a density keeper has the
small power loss needed for summing the dyadic density thresholds. -/
noncomputable section
namespace LipschitzHilbert

def densitySpatialCount (eta : ℝ) : ℕ := ⌈5*densityRadius eta⌉₊

theorem densitySpatialCount_covers (eta : ℝ) :
    5*densityRadius eta≤(densitySpatialCount eta : ℝ) := Nat.le_ceil _

theorem densityRadius_sq_le {eta : ℝ} (heta : 0<eta) :
    (densityRadius eta)^2 ≤ densityRadiusConstant^2*(1+eta^(-(1/20:ℝ))) := by
  let x := eta^(-(1/100:ℝ))
  have hx : 0<x := Real.rpow_pos_of_pos heta _
  have hxsq : x^2=eta^(-(1/50:ℝ)) := by
    dsimp only [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul heta.le]
    norm_num
  have hm : (max 1 x)^2≤1+eta^(-(1/20:ℝ)) := by
    by_cases he : eta≤1
    · have hxone : 1≤x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos heta he (by norm_num)
      rw [max_eq_right hxone,hxsq]
      have h := Real.rpow_le_rpow_of_exponent_ge heta he (by norm_num : -(1/20:ℝ)≤ -(1/50:ℝ))
      linarith
    · have hxone : x≤1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge he) (by norm_num)
      rw [max_eq_left hxone,one_pow]
      linarith [Real.rpow_nonneg heta.le (-(1/20:ℝ))]
  dsimp only [densityRadius]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)

theorem densitySpatialCost_le {eta : ℝ} (heta : 0<eta) :
    ((((4*densitySpatialCount eta+1)^2 : ℕ) : ℝ)) ≤
      (625*densityRadiusConstant^2)*(1+eta^(-(1/20:ℝ))) := by
  have hK := densityRadius_ge_one eta
  have hceil : (densitySpatialCount eta : ℝ)≤5*densityRadius eta+1 :=
    (Nat.ceil_lt_add_one (by linarith : 0≤5*densityRadius eta)).le
  have hlin : 4*(densitySpatialCount eta : ℝ)+1≤25*densityRadius eta := by linarith
  have hsquare : (4*(densitySpatialCount eta : ℝ)+1)^2≤625*(densityRadius eta)^2 := by
    nlinarith [sq_nonneg (25*densityRadius eta-(4*(densitySpatialCount eta : ℝ)+1))]
  push_cast
  calc
    _ ≤ 625*(densityRadius eta)^2 := hsquare
    _ ≤ 625*(densityRadiusConstant^2*(1+eta^(-(1/20:ℝ)))) :=
      mul_le_mul_of_nonneg_left (densityRadius_sq_le heta) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
