import OAI.MeasureTheory.Falconer.Measures.WeightedIntegralSquare

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

 theorem integrable_coeff_norm_power {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ) (hF : Measurable F)
    {C : ℝ} (_ : 0 ≤ C) (hb : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    Integrable (fun x => ‖c x‖ * ‖F x‖^n) μ := by
  apply (hic.norm.mul_const (C^n)).mono'
    (hic.aestronglyMeasurable.norm.mul (hF.aestronglyMeasurable.norm.pow n))
  filter_upwards with x
  change ‖‖c x‖ * ‖F x‖^n‖ ≤ ‖c x‖ * C^n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb x) n) (norm_nonneg _)

 theorem continuous_coefficient_shell_square (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : Plane → ℂ) (hc : Measurable c) (hic : Integrable c)
    (F : Plane × ℝ → ℂ) (hF : Measurable F)
    {C B : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖F p‖ ≤ C)
    (hB : ∀ ξ, (∫ r, ‖F (ξ,r)‖^2 ∂μ) ≤ B) :
    (∫ r, ‖∫ ξ, c ξ * F (ξ,r)‖^2 ∂μ) ≤ (∫ ξ, ‖c ξ‖)^2 * B := by
  let W := ∫ ξ, ‖c ξ‖
  have hW : 0 ≤ W := integral_nonneg (fun _ => norm_nonneg _)
  have hiJoint : Integrable (fun p : Plane × ℝ => ‖c p.1‖ * ‖F p‖^2)
      (volume.prod μ) := by
    apply ((hic.norm.comp_fst μ).mul_const (C^2)).mono'
      ((hic.aestronglyMeasurable.norm.comp_fst).mul (hF.aestronglyMeasurable.norm.pow 2))
    filter_upwards with p
    change ‖‖c p.1‖ * ‖F p‖^2‖ ≤ ‖c p.1‖ * C^2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb p) 2) (norm_nonneg _)
  have hPoint (r : ℝ) : ‖∫ ξ, c ξ * F (ξ,r)‖^2 ≤
      W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2) := by
    have hmF : Measurable (fun ξ => F (ξ,r)) := hF.comp (measurable_id.prodMk measurable_const)
    have hi₁ := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic hmF hC (fun ξ => hb (ξ,r)) 1
    have hi₂ := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic hmF hC (fun ξ => hb (ξ,r)) 2
    exact norm_integral_coeff_square volume c (fun ξ => F (ξ,r)) hic
      (by simpa only [pow_one] using hi₁) hi₂
  have hm : Measurable (fun r => ∫ ξ, c ξ * F (ξ,r)) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  have hiBound : Integrable (fun r => W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2)) μ :=
    hiJoint.integral_prod_right.const_mul W
  have hiMix : Integrable (fun r => ‖∫ ξ, c ξ * F (ξ,r)‖^2) μ :=
    hiBound.mono' (hm.norm.pow_const 2).aestronglyMeasurable (by
      filter_upwards with r
      change ‖‖∫ ξ, c ξ * F (ξ,r)‖^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖∫ ξ, c ξ * F (ξ,r)‖))]
      exact hPoint r)
  calc
    _ ≤ ∫ r, W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2) ∂μ :=
      integral_mono hiMix hiBound hPoint
    _ = W * (∫ ξ, ‖c ξ‖ * (∫ r, ‖F (ξ,r)‖^2 ∂μ)) := by
      rw [integral_const_mul, ← integral_integral_swap
        (f := fun ξ r => ‖c ξ‖ * ‖F (ξ,r)‖^2) hiJoint]
      simp_rw [integral_const_mul]
    _ ≤ W * (∫ ξ, ‖c ξ‖ * B) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply integral_mono
      · simpa only [integral_const_mul] using hiJoint.integral_prod_left
      · exact hic.norm.mul_const B
      · intro ξ
        exact mul_le_mul_of_nonneg_left (hB ξ) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; dsimp [W]; ring

end PlanarFalconer

end OAI
