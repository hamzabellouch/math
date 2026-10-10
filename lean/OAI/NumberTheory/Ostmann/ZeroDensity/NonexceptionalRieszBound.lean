import OAI.NumberTheory.Ostmann.ZeroDensity.RieszRectangleBound
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroFreeLogDerivative

namespace OAI

/-! # The nonexceptional Riesz estimate from the actual zero-free region -/

namespace Ostmann

open Complex Set
open scoped Interval

theorem nonexceptional_character_riesz_bound : ∃ c A B E : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ Q : ℕ, 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
      ∀ X b : ℝ, 1 ≤ X → 1 < b → b ≤ 2 →
      let H := Real.log (2 * (Q : ℝ) * (T + 2))
      ‖characterRieszMean χ X‖ ≤ A * H ^ 2 * X ^ (1 - c / H) +
        B * H ^ 2 * X ^ b / T ^ 2 + 2 * (1 / (b - 1) + E) * X ^ b / T := by
  obtain ⟨c0, M0, hc0, hM0, hdata⟩ := character_zero_free_logDeriv_data
  obtain ⟨K, E, hK, hE, hrect⟩ := characterRieszMean_rectangle_bound
  let c := min c0 (1 / 4)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hcc0 : c ≤ c0 := min_le_left _ _
  have hc4 : c ≤ 1 / 4 := min_le_right _ _
  refine ⟨c, K * M0, 4 * M0, E, hc, hc4, by positivity, by positivity, hE, ?_⟩
  intro Q hQ T hT
  obtain ⟨exception, he⟩ := hdata Q hQ T hT
  refine ⟨exception, ?_⟩
  intro χ hχ hne X b hX hb hb2
  dsimp only
  let H := Real.log (2 * (Q : ℝ) * (T + 2))
  let a := 1 - c / H
  have hH : 1 ≤ H := conductor_height_log_ge_one Q (by omega) (T + 2) (by linarith)
  have hHp : 0 < H := by linarith
  have ha : 1 / 2 ≤ a := by
    have hh : c / H ≤ 1 / 4 := calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ 1 / 4 := by simpa using hc4
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 := by
    have hh : 0 ≤ c / H := by positivity
    dsimp [a]
    linarith
  have hab : a ≤ b := ha1.trans hb.le
  have hpoint (z : ℂ) (hz : z ∈ uIcc a b ×ℂ uIcc (-T) T) :
      χ.L z ≠ 0 ∧ ‖logDeriv χ.L z‖ ≤ M0 * H ^ 2 := by
    have hzre : a ≤ z.re ∧ z.re ≤ b := by simpa [uIcc_of_le hab] using hz.1
    have hzim : -T ≤ z.im ∧ z.im ≤ T := by
      simpa [uIcc_of_le (show -T ≤ T by linarith)] using hz.2
    have hf := div_le_div_of_nonneg_right hcc0 hHp.le
    apply he χ hχ hne z
    · change 1 - c0 / H ≤ z.re
      dsimp [a] at hzre
      linarith
    · exact hzre.2.trans hb2
    · exact abs_le.mpr hzim
  have hr := hrect χ X a b T (M0 * H ^ 2) hX ha hab hb hb2
    (by linarith) (by positivity) (fun z hz => (hpoint z hz).1) (fun z hz => (hpoint z hz).2)
  have hlen : b - a ≤ 2 := by linarith
  have hterm : 2 * (M0 * H ^ 2 * X ^ b / T ^ 2) * (b - a) ≤
      4 * M0 * H ^ 2 * X ^ b / T ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hlen
      (by positivity : 0 ≤ 2 * (M0 * H ^ 2 * X ^ b / T ^ 2))
    convert hh using 1
    ring
  calc
    _ ≤ K * (M0 * H ^ 2) * X ^ a +
        2 * (M0 * H ^ 2 * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + E) * X ^ b / T := hr
    _ ≤ K * (M0 * H ^ 2) * X ^ a +
        4 * M0 * H ^ 2 * X ^ b / T ^ 2 +
        2 * (1 / (b - 1) + E) * X ^ b / T := by linarith
    _ = _ := by dsimp [a, H]; ring

end Ostmann

end OAI
