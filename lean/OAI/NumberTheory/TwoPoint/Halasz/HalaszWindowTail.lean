import OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowIntegral

namespace OAI

/-! Absolute truncation of the narrow Perron integral. The inverse-square
tail gives an explicit error, independently of the central mean squares. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_cauchy_tail_right {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ioi T, (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  rw [integral_Ioi_inv_one_add_sq, ← Real.arctan_inv_of_pos hT]
  exact Real.arctan_le_self (by positivity)

lemma halasz_cauchy_tail_left {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Iic (-T), (1 + t ^ 2)⁻¹) ≤ T⁻¹ := by
  rw [integral_Iic_inv_one_add_sq, Real.arctan_neg]
  have h := halasz_cauchy_tail_right hT
  rw [integral_Ioi_inv_one_add_sq] at h
  linarith

theorem halasz_integral_truncate (f : ℝ → ℂ) (hf : Integrable f)
    {T D : ℝ} (hT : 0 < T) (hD : 0 ≤ D)
    (hbound : ∀ t, ‖f t‖ ≤ D * (1 + t ^ 2)⁻¹) :
    ‖∫ t : ℝ, f t‖ ≤ ‖∫ t in -T..T, f t‖ + 2 * D / T := by
  have hmajor := integrable_inv_one_add_sq.const_mul D
  have hleft : ‖∫ t in Set.Iic (-T), f t‖ ≤ D / T := by
    calc
      _ ≤ ∫ t in Set.Iic (-T), D * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajor.restrict (Filter.Eventually.of_forall hbound)
      _ = D * ∫ t in Set.Iic (-T), (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ D * T⁻¹ := mul_le_mul_of_nonneg_left (halasz_cauchy_tail_left hT) hD
      _ = _ := by rw [div_eq_mul_inv]
  have hright : ‖∫ t in Set.Ioi T, f t‖ ≤ D / T := by
    calc
      _ ≤ ∫ t in Set.Ioi T, D * (1 + t ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajor.restrict (Filter.Eventually.of_forall hbound)
      _ = D * ∫ t in Set.Ioi T, (1 + t ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ D * T⁻¹ := mul_le_mul_of_nonneg_left (halasz_cauchy_tail_right hT) hD
      _ = _ := by rw [div_eq_mul_inv]
  have hsplit : (∫ t : ℝ, f t) = (∫ t in Set.Iic (-T), f t) +
      (∫ t in -T..T, f t) + ∫ t in Set.Ioi T, f t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic hf.restrict hf.restrict,
      add_sub_cancel, intervalIntegral.integral_Iic_add_Ioi hf.restrict hf.restrict]
  rw [hsplit]
  have hn := (norm_add_le ((∫ t in Set.Iic (-T), f t) + ∫ t in -T..T, f t)
    (∫ t in Set.Ioi T, f t)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  rw [mul_div_assoc]
  linarith

theorem halasz_window_integral_truncate (P Q F : ℝ → ℂ)
    {x δ T U V W : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hT : 0 < T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hP : ∀ t, ‖P t‖ ≤ U) (hQ : ∀ t, ‖Q t‖ ≤ V) (hF : ∀ t, ‖F t‖ ≤ W)
    (hint : Integrable (fun t : ℝ => P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I))) :
    ‖∫ t : ℝ, P t * Q t * F t *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      ‖∫ t in -T..T, P t * Q t * F t *
        halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ +
        40 * x * U * V * W / (δ * T) := by
  refine (halasz_integral_truncate _ hint hT
    (show 0 ≤ U * V * W * (20 * x / δ) by positivity) ?_).trans_eq ?_
  · intro t
    rw [norm_mul, norm_mul, norm_mul]
    calc
      _ ≤ U * V * W * (20 * x / (δ * (1 + t ^ 2))) := by
        exact mul_le_mul
          (mul_le_mul (mul_le_mul (hP t) (hQ t) (norm_nonneg _) hU)
            (hF t) (norm_nonneg _) (mul_nonneg hU hV))
          (halasz_perron_window_tail hx hδ hδ1 t) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hU hV) hW)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  · congr 1
    ring

end TwoPointCorrelations

end OAI
