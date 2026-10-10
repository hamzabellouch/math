import OAI.Probability.FreeIsing.Energy.ShiftedFieldVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def shiftedLossCoefficient (theta beta : ℝ) : ℝ :=
  (1 - theta ^ 2) /
    (Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2)

lemma shiftedLossCoefficient_pos {theta beta : ℝ} (hθ : theta ^ 2 < 1) :
    0 < shiftedLossCoefficient theta beta := by
  apply div_pos (sub_pos.mpr hθ)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)

lemma integral_shifted_attenuation_loss_explicit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {theta beta : ℝ} {G : Ω → ℝ} (hθ : theta ^ 2 ≤ 1)
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) (z : ℝ) :
    (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
      1 - shiftedLossCoefficient theta beta * variance G μ := by
  let C : ℝ := Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2
  have hC : 0 < C :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)
  have hv := variance_le_uniform_tanh_shift_integral hG hBound z
  have hcoef : 0 ≤ (1 - theta ^ 2) / C := div_nonneg (sub_nonneg.mpr hθ) (le_of_lt hC)
  have h := mul_le_mul_of_nonneg_left hv hcoef
  have hcancel : (1 - theta ^ 2) / C *
      (C * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ) =
      (1 - theta ^ 2) * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
    rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hC)]
  change (1 - theta ^ 2) / C * variance G μ ≤ _ at h
  rw [hcancel] at h
  have hi := integral_responseAttenuation_shift_sq_le (μ := μ) hθ hG (z := z)
  change (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
    1 - ((1 - theta ^ 2) / C) * variance G μ
  linarith

section Conditional

variable {Ω B : Type*} {mΩ : MeasurableSpace Ω} {mB : MeasurableSpace B}
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → B} {G : Ω → ℝ}

lemma ae_condDistrib_abs_le {beta : ℝ} (hX : Measurable X) (hG : Measurable G)
    (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) :
    ∀ᵐ w ∂μ, ∀ᵐ y ∂condDistrib G X μ (X w), |y| ≤ beta := by
  have hmap : ∀ᵐ y ∂μ.map G, |y| ≤ beta :=
    (ae_map_iff hG.aemeasurable (measurableSet_le measurable_id.abs measurable_const)).mpr hBound
  rw [← condDistrib_comp_map hX.aemeasurable hG.aemeasurable] at hmap
  exact ae_of_ae_map hX.aemeasurable (Measure.ae_ae_of_ae_comp hmap)

lemma condExp_shifted_attenuation_le_condDistrib_variance
    {theta beta : ℝ} (hθ : theta ^ 2 ≤ 1)
    (hX : Measurable X) (hG : Measurable G) {shift : B → ℝ} (hs : Measurable shift)
    (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta (shift (X v) + G v) ^ 2 | mB.comap X]) w ≤
        1 - shiftedLossCoefficient theta beta * variance id (condDistrib G X μ (X w)) := by
  let F : B × ℝ → ℝ := fun p => responseAttenuation theta (shift p.1 + p.2) ^ 2
  have hFm : Measurable F :=
    ((continuous_responseAttenuation hθ).measurable.comp
      ((hs.comp measurable_fst).add measurable_snd)).pow_const 2
  have hFi : Integrable (fun w => F (X w, G w)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (hFm.comp (hX.prodMk hG)).aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := responseAttenuation_pos hθ (shift (X w) + G w)
    have hle := responseAttenuation_le_one hθ (shift (X w) + G w)
    change responseAttenuation theta (shift (X w) + G w) ^ 2 ≤ 1
    nlinarith
  have hCE := condExp_prod_ae_eq_integral_condDistrib hX hG.aemeasurable
    hFm.stronglyMeasurable hFi
  filter_upwards [hCE, ae_condDistrib_abs_le hX hG hBound] with w hw hsupport
  change (μ[fun v => F (X v, G v) | mB.comap X]) w ≤ _
  rw [hw]
  exact integral_shifted_attenuation_loss_explicit hθ measurable_id hsupport (shift (X w))

lemma condDistrib_variance_eq_condExp_sq_sub {beta : ℝ}
    (hX : Measurable X) (hG : Measurable G)
    (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) :
    ∀ᵐ w ∂μ, variance id (condDistrib G X μ (X w)) =
      (μ[fun v => G v ^ 2 | mB.comap X]) w - ((μ[G | mB.comap X]) w) ^ 2 := by
  have hMem : MemLp G 2 μ := MemLp.of_bound hG.aestronglyMeasurable beta
    (by simpa only [Real.norm_eq_abs] using hBound)
  have hCE1 := condExp_ae_eq_integral_condDistrib' hX (hMem.integrable one_le_two)
  have hCE2 := condExp_ae_eq_integral_condDistrib hX hG.aemeasurable
    (measurable_id.pow_const 2).stronglyMeasurable hMem.integrable_sq
  filter_upwards [hCE1, hCE2, ae_condDistrib_abs_le hX hG hBound] with w hw1 hw2 hsupport
  have hcondMem : MemLp (id : ℝ → ℝ) 2 (condDistrib G X μ (X w)) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable beta
      (by simpa only [Real.norm_eq_abs, id_eq] using hsupport)
  simp only [id_eq] at hw2
  rw [variance_eq_sub hcondMem, hw1, hw2]
  rfl

lemma condExp_shifted_attenuation_le_condVariance
    {theta beta : ℝ} (hθ : theta ^ 2 ≤ 1)
    (hX : Measurable X) (hG : Measurable G) {shift : B → ℝ} (hs : Measurable shift)
    (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) :
    ∀ᵐ w ∂μ,
      (μ[fun v => responseAttenuation theta (shift (X v) + G v) ^ 2 | mB.comap X]) w ≤
        1 - shiftedLossCoefficient theta beta *
          ((μ[fun v => G v ^ 2 | mB.comap X]) w - ((μ[G | mB.comap X]) w) ^ 2) := by
  filter_upwards [condExp_shifted_attenuation_le_condDistrib_variance hθ hX hG hs hBound,
    condDistrib_variance_eq_condExp_sq_sub hX hG hBound] with w hw hvar
  rwa [hvar] at hw

end Conditional

end Problem367

end

end OAI
