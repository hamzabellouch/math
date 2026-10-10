import OAI.MeasureTheory.Falconer.Shells.ListWeightedShell

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem shell_multiplier_square (μ : Measure ℝ) (u F : ℝ → ℂ)
    (hu : Measurable u) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) μ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ r ∂μ, ‖u r‖ ≤ A) :
    Integrable (fun r => ‖u r*F r‖^2) μ ∧
      (∫ r, ‖u r*F r‖^2 ∂μ) ≤ A^2*(∫ r, ‖F r‖^2 ∂μ) := by
  have hp : ∀ᵐ r ∂μ, ‖u r*F r‖^2 ≤ A^2*‖F r‖^2 := by
    filter_upwards [hb] with r hr
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hA).mpr hr) (sq_nonneg _)
  have hi' : Integrable (fun r => ‖u r*F r‖^2) μ := by
    apply (hi.const_mul (A^2)).mono' ((hu.mul hF).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with r hr
    change ‖‖u r*F r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  exact ⟨hi', (integral_mono_ae hi' (hi.const_mul (A^2)) hp).trans_eq (integral_const_mul _ _)⟩

theorem continuous_shell_mixture_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : Plane → ℂ) (hc : Measurable c) (hic : Integrable c)
    (F : Plane × ℝ → ℂ) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖F p‖ ≤ C) :
    Measurable (fun r => ∫ ξ, c ξ*F (ξ,r)) ∧
    (∀ r, ‖∫ ξ, c ξ*F (ξ,r)‖ ≤ (∫ ξ, ‖c ξ‖)*C) ∧
    Integrable (fun r => ‖∫ ξ, c ξ*F (ξ,r)‖^2) μ := by
  have hm : Measurable (fun r => ∫ ξ, c ξ*F (ξ,r)) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  have hn (r : ℝ) : ‖∫ ξ, c ξ*F (ξ,r)‖ ≤ (∫ ξ, ‖c ξ‖)*C := by
    apply (norm_integral_le_integral_norm _).trans
    simp only [norm_mul]
    have hi := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic
      (hF.comp (measurable_id.prodMk measurable_const)) hC (fun ξ => hb (ξ,r)) 1
    apply (integral_mono (by simpa using hi) (hic.norm.mul_const C)
      (fun ξ => mul_le_mul_of_nonneg_left (hb (ξ,r)) (norm_nonneg _))).trans_eq
    exact integral_mul_const _ _
  refine ⟨hm,hn,?_⟩
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable
    (((∫ ξ, ‖c ξ‖)*C)^2)
  filter_upwards with r
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hn r) 2

end PlanarFalconer

end OAI
