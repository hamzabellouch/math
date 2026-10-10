import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothZeroSplit

namespace OAI

/-! # The smooth character mean with all zero contributions displayed -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothTrivialZeroTerm_norm_le {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter) :
    ‖smoothTrivialZeroTerm χ‖ ≤ P.mellinConstant := by
  have hh := P.mellin_decay 0 (by norm_num) (by norm_num)
  simp only [Complex.zero_im, abs_zero, add_zero, Real.log_one, mul_zero,
    Real.exp_zero, mul_one] at hh
  unfold smoothTrivialZeroTerm
  split_ifs
  · exact hh
  · simpa only [norm_zero] using P.mellinConstant_pos.le

theorem smooth_character_bounded_height {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter)
    (X T : ℝ) (hX : 2 ≤ X) :
    ‖smoothMangoldtMean χ.modulus χ.character X‖ ≤
      (∑ i ∈ (Z χ).heightIndices T, ‖smoothZeroTerm Z χ X i‖) +
      (∑' i, if T ≤ |((Z χ).zeros i).im| then ‖smoothZeroTerm Z χ X i‖ else 0) +
      P.mellinConstant + P.errorConstant / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ)) := by
  have htri : ‖smoothMangoldtMean χ.modulus χ.character X‖ ≤
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ +
        ‖∑' i, smoothZeroTerm Z χ X i‖ + ‖smoothTrivialZeroTerm χ‖ := by
    have he : smoothMangoldtMean χ.modulus χ.character X =
        (smoothMangoldtMean χ.modulus χ.character X +
          (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ) -
          (∑' i, smoothZeroTerm Z χ X i) - smoothTrivialZeroTerm χ := by ring
    calc
      _ = ‖(smoothMangoldtMean χ.modulus χ.character X +
          (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ) -
          (∑' i, smoothZeroTerm Z χ X i) - smoothTrivialZeroTerm χ‖ := congrArg norm he
      _ ≤ _ := (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  have hn := norm_tsum_le_tsum_norm (P.absolute_summability χ X hX)
  have hz := nonnegative_tsum_finite_tail_bound (fun i => ‖smoothZeroTerm Z χ X i‖)
    (fun _ => norm_nonneg _) (P.absolute_summability χ X hX) ((Z χ).heightIndices T)
    (fun i => T ≤ |((Z χ).zeros i).im|) (fun i hi => by
      have hh : ¬ |((Z χ).zeros i).im| ≤ T := by
        simpa only [ComplexZeroEnumeration.mem_heightIndices] using hi
      exact (lt_of_not_ge hh).le)
  linarith [P.explicit_formula χ X hX, smoothTrivialZeroTerm_norm_le P χ]

theorem smooth_nonprincipal_family_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (T X : ℝ) (hT : 0 ≤ T) (hX : 2 ≤ X) :
    (∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character X‖) ≤
      (X * P.mellinConstant) *
        (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices T).filter
          (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
            Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re))) +
      (Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant) *
        (P.zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2))) +
      (X * P.mellinConstant) *
        (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
          Real.exp (-4 * Real.log (1 + T))) +
      (F.card : ℝ) * (P.mellinConstant + P.errorConstant / Real.sqrt X * Real.log (2 * (Q : ℝ))) := by
  have hQp : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hX1 : 1 ≤ X := by linarith
  have hpoint (χ) (hχ : χ ∈ F) :
      ‖smoothMangoldtMean χ.modulus χ.character X‖ ≤
      (X * P.mellinConstant) *
        (∑ i ∈ ((Z χ).heightIndices T).filter (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
          Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re))) +
      (Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant) *
        ((Z χ).heightIndices T).card +
      (∑' i, if T ≤ |((Z χ).zeros i).im| then ‖smoothZeroTerm Z χ X i‖ else 0) +
      (P.mellinConstant + P.errorConstant / Real.sqrt X * Real.log (2 * (Q : ℝ))) := by
    have ht := smooth_character_bounded_height P χ X T hX
    have hz := bounded_height_zero_norm_sum P χ T X hX1
    have hlog : Real.log (2 * (χ.modulus : ℝ)) ≤ Real.log (2 * (Q : ℝ)) := by
      apply Real.log_le_log (by have hp := χ.positive; positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hF χ hχ) (by norm_num)
    have he := mul_le_mul_of_nonneg_left hlog
      (div_nonneg P.errorConstant_pos.le (Real.sqrt_nonneg X))
    linarith
  have hh := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
  have hc : (∑ χ ∈ F, (((Z χ).heightIndices T).card : ℝ)) ≤
      P.zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2)) := by
    have he (χ : PrimitiveComplexCharacter) : ((Z χ).heightIndices T).card =
        (Z χ).count 0 T := by
      unfold ComplexZeroEnumeration.count
      rw [Finset.filter_eq_self.mpr (fun i _ => ((Z χ).in_strip i).1.le)]
    simp only [he]
    exact P.zero_count Q hQ T hT F hF
  have hc' := mul_le_mul_of_nonneg_left hc
    (mul_nonneg (Real.exp_nonneg ((1 / 2 : ℝ) * Real.log X)) P.mellinConstant_pos.le)
  have hhigh := high_smooth_zero_tsum_bound P Q hQ F hF T X hT hX1
  linarith

end Ostmann

end OAI
