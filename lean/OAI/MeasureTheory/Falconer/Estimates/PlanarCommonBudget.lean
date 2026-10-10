import OAI.MeasureTheory.Falconer.Geometry.PlanarGridCosts

namespace OAI

/-! One fixed polynomial majorizes the separate rounding, regularity,
density and directional losses in the planar graph application. -/
namespace Falconer

 theorem planar_common_budget {W M : ℝ} (hW : 1 ≤ W) (hM : 1 ≤ M) :
    let B := 4000000*W^5*M^6
    M ≤ B ∧ 429025*W*M^2 ≤ B ∧ 3003175*W*M^6 ≤ B ∧
      262144*W*M^6 ≤ B ∧ 4096*W^2*M^4 ≤ B ∧ 429025*W^2*M^2 ≤ B := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hW5 : 1 ≤ W^5 := one_le_pow₀ hW
  have hM6 : 1 ≤ M^6 := one_le_pow₀ hM
  have hWW : W ≤ W^5 := by simpa only [pow_one] using pow_le_pow_right₀ hW (show 1 ≤ (5:ℕ) by omega)
  have hW2 : W^2 ≤ W^5 := pow_le_pow_right₀ hW (by omega)
  have hMM : M ≤ M^6 := by simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ (6:ℕ) by omega)
  have hM2 : M^2 ≤ M^6 := pow_le_pow_right₀ hM (by omega)
  have hM4 : M^4 ≤ M^6 := pow_le_pow_right₀ hM (by omega)
  have hprod : 0 ≤ W^5*M^6 := by positivity
  have hcoeff (c : ℝ) (hc : 0 ≤ c) (hcB : c ≤ 4000000) (x y : ℝ)
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hxW : x ≤ W^5) (hyM : y ≤ M^6) :
      c*x*y ≤ 4000000*W^5*M^6 := by
    calc
      _ = c*(x*y) := by ring
      _ ≤ c*(W^5*M^6) := mul_le_mul_of_nonneg_left (mul_le_mul hxW hyM hy (by positivity)) hc
      _ ≤ 4000000*(W^5*M^6) := mul_le_mul_of_nonneg_right hcB hprod
      _ = _ := by ring
  refine ⟨?_,hcoeff 429025 (by norm_num) (by norm_num) W (M^2) hW0 (by positivity) hWW hM2,
    hcoeff 3003175 (by norm_num) (by norm_num) W (M^6) hW0 (by positivity) hWW le_rfl,
    hcoeff 262144 (by norm_num) (by norm_num) W (M^6) hW0 (by positivity) hWW le_rfl,
    hcoeff 4096 (by norm_num) (by norm_num) (W^2) (M^4) (by positivity) (by positivity) hW2 hM4,
    hcoeff 429025 (by norm_num) (by norm_num) (W^2) (M^2) (by positivity) (by positivity) hW2 hM2⟩
  have hh := hcoeff 1 (by norm_num) (by norm_num) 1 M (by norm_num) hM0 hW5 hMM
  simpa only [one_mul] using hh

end Falconer

end OAI
