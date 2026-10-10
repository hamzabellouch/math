import OAI.NumberTheory.Ostmann.Characters.CharacterLogarithmicSeparation
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualComplexZeroRegion

namespace OAI

/-! # Uniform logarithmic derivatives in the zero-free rectangle

One exceptional character is omitted. All other primitive characters have
an explicit log-squared bound on the right-hand contour rectangle.
-/

namespace Ostmann

open Complex

theorem character_zero_free_logDeriv_data : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ Q : ℕ, 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
      ∀ s : ℂ, 1 - c / Real.log (2 * (Q : ℝ) * (T + 2)) ≤ s.re → s.re ≤ 2 →
        |s.im| ≤ T → χ.L s ≠ 0 ∧ ‖logDeriv χ.L s‖ ≤
          C * (Real.log (2 * (Q : ℝ) * (T + 2))) ^ 2 := by
  obtain ⟨c0, hc0, hregion⟩ := actualComplexZeroRegion
  obtain ⟨C0, hC0, hsepbound⟩ := character_logDeriv_logarithmic_separation
  let c := min (c0 / 4) (1 / 4)
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc0 : 4 * c ≤ c0 := by have hh := min_le_left (c0 / 4) (1 / 4); dsimp [c]; linarith
  have hcquarter : c ≤ 1 / 4 := min_le_right _ _
  refine ⟨c, 3 * C0 * (1 + c⁻¹), hc, by positivity, ?_⟩
  intro Q hQ T hT
  obtain ⟨exception, hexception⟩ := hregion Q hQ (T + 2) (by linarith)
  refine ⟨exception, ?_⟩
  intro χ hχ hne s hs hs2 ht
  let H := Real.log (2 * (Q : ℝ) * (T + 2))
  have hH : 1 ≤ H := conductor_height_log_ge_one Q (by omega) (T + 2) (by linarith)
  have hHp : 0 < H := by linarith
  let δ := c / H
  have hδ : 0 < δ := div_pos hc hHp
  have hδquarter : δ ≤ 1 / 4 := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ 1 / 4 := by simpa using hcquarter
  have hspos : 1 / 2 ≤ s.re := by change 1 - δ ≤ s.re at hs; linarith
  have hsep (i : ℕ) : δ ≤ ‖s - (actualCharacterZeros χ).zeros i‖ := by
    by_cases hi : |((actualCharacterZeros χ).zeros i).im| ≤ T + 2
    · have hzero := hexception χ hχ hne i hi
      have hfrac : 4 * δ ≤ c0 / H := by
        change 4 * (c / H) ≤ c0 / H
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hcc0 hHp.le
      have hre : δ ≤ (s - (actualCharacterZeros χ).zeros i).re := by
        change 1 - δ ≤ s.re at hs
        change c0 / H ≤ _ at hzero
        simp only [Complex.sub_re]
        linarith
      exact hre.trans (Complex.re_le_norm _)
    · have hi' : T + 2 < |((actualCharacterZeros χ).zeros i).im| := lt_of_not_ge hi
      have htri := abs_add_le (s.im - ((actualCharacterZeros χ).zeros i).im) (-s.im)
      have hdist := Complex.abs_im_le_norm (s - (actualCharacterZeros χ).zeros i)
      rw [show s.im - ((actualCharacterZeros χ).zeros i).im + -s.im =
        -((actualCharacterZeros χ).zeros i).im by ring, abs_neg, abs_neg] at htri
      simp only [Complex.sub_im] at hdist
      linarith
  have hcn : χ.completed s ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
    have hh := hsep i
    rw [hi, sub_self, norm_zero] at hh
    linarith
  refine ⟨?_, ?_⟩
  · rw [χ.L_eq_completed_mul_all]
    exact mul_ne_zero hcn (χ.gammaInverse_ne_zero s (by linarith))
  · have hb := hsepbound χ s δ hspos hs2 hδ hsep

    have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    have hqlog : Real.log χ.modulus ≤ H := by
      apply Real.log_le_log (by exact_mod_cast χ.positive)
      have hh : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχ
      nlinarith
    have htlog : Real.log (|s.im| + 2) ≤ H := by
      apply Real.log_le_log (by positivity)
      nlinarith [abs_nonneg s.im]
    have hlogs : Real.log χ.modulus + Real.log (|s.im| + 2) + 1 ≤ 3 * H := by linarith
    have hdinv : δ⁻¹ = H * c⁻¹ := by dsimp [δ]; rw [inv_div]; ring
    have hcost : 1 + δ⁻¹ ≤ H * (1 + c⁻¹) := by rw [hdinv]; nlinarith
    calc
      _ ≤ C0 * (3 * H) * (H * (1 + c⁻¹)) := by
        apply hb.trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left hlogs hC0.le) hcost
          (by positivity) (by positivity)
      _ = _ := by dsimp [H]; ring

theorem character_zero_free_logDeriv_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ Q : ℕ, 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
      ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
      ∀ s : ℂ, 1 - c / Real.log (2 * (Q : ℝ) * (T + 2)) ≤ s.re → s.re ≤ 2 →
        |s.im| ≤ T → ‖logDeriv χ.L s‖ ≤
          C * (Real.log (2 * (Q : ℝ) * (T + 2))) ^ 2 := by
  obtain ⟨c, C, hc, hC, h⟩ := character_zero_free_logDeriv_data
  refine ⟨c, C, hc, hC, ?_⟩
  intro Q hQ T hT
  obtain ⟨e, he⟩ := h Q hQ T hT
  exact ⟨e, fun χ hχ hne s hs hs2 ht => (he χ hχ hne s hs hs2 ht).2⟩

end Ostmann

end OAI
