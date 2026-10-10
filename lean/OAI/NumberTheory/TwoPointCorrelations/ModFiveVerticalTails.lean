import OAI.NumberTheory.TwoPointCorrelations.ModFiveRightBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace OAI

/-! The two tails of the actual Perron integral.  The inverse-square
majorant is integrated exactly, so no truncation theorem is assumed. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Set Erdos970

lemma modFive_inverse_square_tail {f : ℝ → ℂ} {T D : ℝ}
    (hT : 0 < T) (hbound : ∀ t ∈ Ioi T, ‖f t‖ ≤ D / t ^ 2) :
    ‖∫ t in Ioi T, f t‖ ≤ D / T := by
  have hi : IntegrableOn (fun t : ℝ => D * t ^ (-2 : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul D
  have he : (∫ t in Ioi T, D * t ^ (-2 : ℝ)) = D / T := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  apply (norm_integral_le_of_norm_le hi ?_).trans_eq he
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  convert hbound t ht using 1
  rw [Real.rpow_neg (le_of_lt (hT.trans ht)), Real.rpow_two, div_eq_mul_inv]

lemma modFive_vertical_tails {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 < T)
    (hf : Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)))
    (hbound : ∀ t : ℝ, T ≤ |t| →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / t ^ 2) :
    ‖VerticalIntegral f σ - VIntegral f σ (-T) T‖ ≤ 2 * D / T := by
  have hup : ‖∫ t in Ioi T, f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / T := by
    apply modFive_inverse_square_tail hT
    intro t ht
    exact hbound t (by rw [abs_of_pos (hT.trans ht)]; exact ht.le)
  have hdown : ‖∫ t in Iic (-T), f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / T := by
    rw [← integral_comp_neg_Ioi T]
    apply modFive_inverse_square_tail hT
    intro t ht
    have hb := hbound (-t) (by rw [abs_neg, abs_of_pos (hT.trans ht)]; exact ht.le)
    simpa only [neg_sq] using hb
  have he := verticalIntegral_split_three (f := f) (σ := σ) (-T) T hf
  rw [he]
  have halg (a b c : ℂ) : a + b + c - b = a + c := by ring
  rw [halg]
  calc
    _ ≤ ‖Complex.I • (∫ t in Iic (-T), f ((σ : ℂ) + (t : ℂ) * Complex.I))‖ +
        ‖Complex.I • (∫ t in Ici T, f ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = ‖∫ t in Iic (-T), f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
        ‖∫ t in Ioi T, f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_smul, norm_smul, norm_I, one_mul, one_mul, integral_Ici_eq_integral_Ioi]
    _ ≤ D / T + D / T := add_le_add hdown hup
    _ = _ := by ring

lemma modFive_perron_integrable (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {x σ B : ℝ} (hx : 0 < x) (hσ : 1 < σ) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B) :
    Integrable (fun t : ℝ => modFivePerronIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc : Continuous (fun t : ℝ =>
      modFivePerronIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hsr : 1 ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ.le
    have hn := χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hsr
    have h0 : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, zero_re] at hr
      linarith
    have h1 : (σ : ℂ) + (t : ℂ) * Complex.I + 1 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
        one_re, zero_re] at hr
      linarith
    have hline : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) t := by
      fun_prop
    exact (modFive_perron_integrand_differentiableAt χ hχ hx hn h0 h1).continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) hline
  have hi : Integrable (fun t : ℝ => B * (4 * x ^ σ / (1 + t ^ 2))) := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      (integrable_inv_one_add_sq.const_mul (B * (4 * x ^ σ)))
  apply hi.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [modFivePerronIntegrand, norm_mul]
    exact mul_le_mul (hbound t) (modFive_perron_kernel_vertical hx (by linarith) t)
      (norm_nonneg _) hB

/-- Uniform tails of the actual nonprincipal Perron integrals. -/
theorem modFive_perron_tail_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ δ x T : ℝ,
      0 < δ → 0 < x → 0 < T →
      ‖VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ) -
        VIntegral (modFivePerronIntegrand χ x) (1 + δ) (-T) T‖ ≤
          2 * (1 / δ + C) * x ^ (1 + δ) / T := by
  obtain ⟨C, hC, hb⟩ := modFive_logderiv_right_bound
  refine ⟨C, hC, ?_⟩
  intro χ hχ δ x T hδ hx hT
  have hB : 0 ≤ 1 / δ + C := by positivity
  have hi := modFive_perron_integrable χ hχ hx (by linarith : 1 < 1 + δ) hB
    (hb χ δ · hδ)
  have ht := modFive_vertical_tails hT hi (D := (1 / δ + C) * x ^ (1 + δ)) ?_
  · simpa only [mul_assoc] using ht
  intro t ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
  rw [modFivePerronIntegrand, norm_mul]
  exact (mul_le_mul (hb χ δ t hδ) (modFive_perron_kernel_horizontal hx (1 + δ) ht0)
    (norm_nonneg _) hB).trans_eq (by ring)

end TwoPointCorrelations

end OAI
