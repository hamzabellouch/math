import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszBound
import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaZeroFreeLogDerivative

namespace OAI

/-! # A quantitative principal Riesz estimate with no prime-distribution input -/

namespace Ostmann

open Complex Set
open scoped Interval

theorem principal_riesz_general_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ T X b : ℝ, 2 ≤ T → 1 ≤ X → 1 < b → b ≤ 2 →
      let H := Real.log (T + 4) + 1
      ‖principalRieszMean X - (X / 2 : ℝ)‖ ≤
        A * H ^ 2 * X ^ (1 - c / H) + B * H ^ 2 * X ^ b / T ^ 2 +
          2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c, M0, hc, hc4, hM0, hdata⟩ := zeta_zero_free_logDeriv_data
  obtain ⟨K, E, hK, hE, hrect⟩ := principalRieszMean_rectangle_bound
  refine ⟨c, K * (M0 + c⁻¹), 4 * (M0 + 1), E, hc, hc4,
    by positivity, by positivity, hE, ?_⟩
  intro T X b hT hX hb hb2
  dsimp only
  let H := Real.log (T + 4) + 1
  let a := 1 - c / H
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ T + 4 by linarith)
    dsimp [H]
    linarith
  have hHp : 0 < H := by linarith
  have hfrac : 0 < c / H := div_pos hc hHp
  have hfrac4 : c / H ≤ 1 / 4 := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ 1 / 4 := by simpa using hc4
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hab : a ≤ b := by linarith
  have hpoint (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc (-T) T) :
      regularizedZeta s ≠ 0 ∧ ‖logDeriv regularizedZeta s‖ ≤ M0 * H ^ 2 := by
    have hre : a ≤ s.re ∧ s.re ≤ b := by simpa [uIcc_of_le hab] using hs.1
    have him : -T ≤ s.im ∧ s.im ≤ T := by
      simpa [uIcc_of_le (show -T ≤ T by linarith)] using hs.2
    exact hdata T hT s hre.1 (hre.2.trans hb2) (abs_le.mpr him)
  have hh := hrect X a b T (M0 * H ^ 2) hX ha ha1 hb hb2 (by linarith) (by positivity)
    (fun s hs => (hpoint s hs).1) (fun s hs => (hpoint s hs).2)
  have hinv : 1 / (1 - a) = H * c⁻¹ := by
    dsimp [a]
    rw [show 1 - (1 - c / H) = c / H by ring, one_div, inv_div]
    ring
  have hlow : M0 * H ^ 2 + 1 / (1 - a) ≤ (M0 + c⁻¹) * H ^ 2 := by
    rw [hinv]
    have hh := mul_nonneg (inv_nonneg.mpr hc.le) (show 0 ≤ H ^ 2 - H by nlinarith)
    nlinarith
  have hhigh : M0 * H ^ 2 + 1 / T ≤ (M0 + 1) * H ^ 2 := by
    have hi : 1 / T ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    nlinarith
  have hlength : b - a ≤ 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hK.le)
    (Real.rpow_nonneg (by linarith : 0 ≤ X) a)
  have hsecond : 2 * ((M0 * H ^ 2 + 1 / T) * X ^ b / T ^ 2) * (b - a) ≤
      4 * (M0 + 1) * H ^ 2 * X ^ b / T ^ 2 := by
    have hmult := mul_le_mul_of_nonneg_right hhigh
      (show 0 ≤ X ^ b / T ^ 2 by positivity)
    have hprod := mul_le_mul hmult hlength (sub_nonneg.mpr hab)
      (show 0 ≤ (M0 + 1) * H ^ 2 * (X ^ b / T ^ 2) by positivity)
    convert mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hfirst' : K * (M0 * H ^ 2 + 1 / (1 - a)) * X ^ a ≤
      (K * (M0 + c⁻¹)) * H ^ 2 * X ^ a := by
    convert hfirst using 1
    ring
  calc
    _ ≤ K * (M0 * H ^ 2 + 1 / (1 - a)) * X ^ a +
        2 * ((M0 * H ^ 2 + 1 / T) * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + E) * X ^ b / T := hh
    _ ≤ (K * (M0 + c⁻¹)) * H ^ 2 * X ^ a +
        4 * (M0 + 1) * H ^ 2 * X ^ b / T ^ 2 +
        2 * (1 / (b - 1) + E) * X ^ b / T := by linarith
    _ = _ := rfl

end Ostmann

end OAI
