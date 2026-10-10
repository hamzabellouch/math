import OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourRegion

namespace OAI

/-! The exact finite rectangle shift, with an explicit horizontal cost.
All functions are complex scalar functions, as needed for the three fixed
nonprincipal Dirichlet L-functions.
-/

namespace TwoPointCorrelations

open Complex Set Erdos970 MeasureTheory intervalIntegral

lemma modFive_rectangle_shift {f : ℂ → ℂ} {a b T : ℝ}
    (hf : DifferentiableOn ℂ f (Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ)))) :
    VIntegral f b (-T) T =
      VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T) := by
  have hz := Erdos970.HolomorphicOn.vanishesOnRectangle hf (subset_refl _)
  simp only [RectangleIntegral, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul,
    zero_sub, sub_zero, add_zero, zero_add] at hz
  linear_combination hz

lemma modFive_rectangle_shift_bound {f : ℂ → ℂ} {a b T B : ℝ}
    (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f (Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ))))
    (hup : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B)
    (hdown : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖VIntegral f b (-T) T‖ ≤ ‖VIntegral f a (-T) T‖ + 2 * B * (b - a) := by
  have htop : ‖HIntegral f a b T‖ ≤ B * (b - a) := by
    have hpoint : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hup σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hbot : ‖HIntegral f a b (-T)‖ ≤ B * (b - a) := by
    have hpoint : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hdown σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [modFive_rectangle_shift hf]
  calc
    _ ≤ ‖VIntegral f a (-T) T + HIntegral f a b T‖ + ‖HIntegral f a b (-T)‖ := norm_sub_le _ _
    _ ≤ (‖VIntegral f a (-T) T‖ + ‖HIntegral f a b T‖) + ‖HIntegral f a b (-T)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by linarith

lemma modFive_vertical_quadratic_bound {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Icc (-T) T, ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / (1 + t ^ 2)) :
    ‖VIntegral f σ (-T) T‖ ≤ D * Real.pi := by
  rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
  have hgi : IntervalIntegrable (fun t : ℝ => D / (1 + t ^ 2)) volume (-T) T := by
    simpa only [div_eq_mul_inv] using (integrable_inv_one_add_sq.const_mul D).intervalIntegrable
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall fun t ht => hf t ⟨ht.1.le, ht.2⟩) hgi
  refine hb.trans ?_
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
  apply mul_le_mul_of_nonneg_left _ hD
  linarith [Real.arctan_lt_pi_div_two T, Real.neg_pi_div_two_lt_arctan (-T)]

end TwoPointCorrelations

end OAI
