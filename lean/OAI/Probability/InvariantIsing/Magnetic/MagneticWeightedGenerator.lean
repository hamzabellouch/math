import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteFourth

namespace OAI

/-! Weighted continuation curvature has a bounded potential in the
physical inverse-mean coordinate. -/

noncomputable section

namespace InvariantIsing

lemma weighted_inverse_continuation_generator
    (a aTime au auu w wt wu wuu ζ : ℝ)
    (ha : aTime + a ^ 2 / 2 * auu + ζ * a ^ 2 = 0)
    (hw : wt + a ^ 2 / 2 * wuu + 2 * a * au * wu + (au ^ 2 + a * auu) * w = 0) :
    (2 * a * aTime * w + a ^ 2 * wt) +
      a ^ 2 / 2 * (2 * (au ^ 2 + a * auu) * w + 4 * a * au * wu + a ^ 2 * wuu) +
      (a * auu + 2 * ζ * a) * (a ^ 2 * w) = 0 := by
  linear_combination 2 * a * w * ha + a ^ 2 * hw

lemma fieldBiasFourth_quotient_bound (h : FieldStep) (b : ℝ) :
    |fieldBiasFourth h b / fieldBiasCurvature h b| ≤
      magneticFourthRatioCap (scalarFieldIncrements h) := by
  rw [abs_div, abs_of_pos (fieldBiasCurvature_pos h b)]
  exact (div_le_iff₀ (fieldBiasCurvature_pos h b)).mpr (fieldBiasFourth_relative h b)

lemma magnetic_weighted_curvature_second_bound (h : FieldStep) (s : ℝ) :
    |magneticCurvature h s * magneticCurvatureSecond h s| ≤
      magneticFourthRatioCap (scalarFieldIncrements h) +
        (magneticThirdRatioCap (scalarFieldIncrements h)) ^ 2 := by
  let b := magneticBias h s
  let q := fieldBiasCurvature h b
  have hq : 0 < q := fieldBiasCurvature_pos h b
  have he : magneticCurvature h s * magneticCurvatureSecond h s =
      fieldBiasFourth h b / q - (fieldBiasThird h b / q) ^ 2 := by
    dsimp only [magneticCurvature, magneticCurvatureSecond, b, q]
    field_simp [(fieldBiasCurvature_pos h (magneticBias h s)).ne']
  have hr : |fieldBiasThird h b / q| ≤ magneticThirdRatioCap (scalarFieldIncrements h) := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (fieldBiasThird_relative h b)
  have hr2 : |(fieldBiasThird h b / q) ^ 2| ≤ (magneticThirdRatioCap (scalarFieldIncrements h)) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (fieldBiasFourth_quotient_bound h b) hr2)

lemma magnetic_weighted_potential_bound (h : FieldStep) {s : ℝ} (hs : |s| < 1) (ζ : ℝ) :
    |magneticCurvature h s * magneticCurvatureSecond h s + 2 * ζ * magneticCurvature h s| ≤
      magneticFourthRatioCap (scalarFieldIncrements h) +
        (magneticThirdRatioCap (scalarFieldIncrements h)) ^ 2 + 2 * |ζ| := by
  have ha := magneticCurvature_le_spin_variance h hs
  have haq : |magneticCurvature h s| ≤ 1 := by
    rw [abs_of_pos (magneticCurvature_pos h s)]
    linarith [sq_nonneg s]
  have ht : |2 * ζ * magneticCurvature h s| ≤ 2 * |ζ| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left haq (by positivity : 0 ≤ 2 * |ζ|)
  exact (abs_add_le _ _).trans (add_le_add (magnetic_weighted_curvature_second_bound h s) ht)

end InvariantIsing

end

end OAI
