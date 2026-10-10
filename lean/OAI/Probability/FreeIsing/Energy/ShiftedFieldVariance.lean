import OAI.Probability.FreeIsing.Energy.Attenuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma strictMono_tanh_response : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh_response x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

lemma tanh_abs_response (x : ℝ) : Real.tanh |x| = |Real.tanh x| := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, abs_div,
    abs_of_pos (Real.cosh_pos x), Real.abs_sinh, Real.cosh_abs]

lemma tanh_one_pos_response : 0 < Real.tanh 1 := by
  have h := strictMono_tanh_response (by norm_num : (0 : ℝ) < 1)
  simpa using h

lemma sq_le_cosh_sq_mul_tanh_sq {x M : ℝ} (hx : |x| ≤ M) :
    x ^ 2 ≤ Real.cosh M ^ 2 * Real.tanh x ^ 2 := by
  have hsinh : |x| ≤ |Real.sinh x| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg x)
  have hcosh : Real.cosh x ≤ Real.cosh M :=
    Real.cosh_le_cosh.mpr (hx.trans (le_abs_self M))
  have heq : |Real.sinh x| = Real.cosh x * |Real.tanh x| := by
    rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x)]
    field_simp
  have h : |x| ≤ Real.cosh M * |Real.tanh x| := by
    rw [heq] at hsinh
    exact hsinh.trans (mul_le_mul_of_nonneg_right hcosh (abs_nonneg _))
  have hsq := (sq_le_sq₀ (abs_nonneg x)
    (mul_nonneg (le_of_lt (Real.cosh_pos M)) (abs_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow] using hsq

lemma tanh_one_sq_le_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    Real.tanh 1 ^ 2 ≤ Real.tanh x ^ 2 := by
  have h := strictMono_tanh_response.monotone hx
  rw [tanh_abs_response] at h
  have hs := (sq_le_sq₀ (le_of_lt tanh_one_pos_response) (abs_nonneg _)).mpr h
  simpa only [sq_abs] using hs

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma integrable_tanh_shift_sq (hG : Measurable G) (z : ℝ) :
    Integrable (fun w => Real.tanh (z + G w) ^ 2) μ := by
  have hm : Measurable (fun w => Real.tanh (z + G w) ^ 2) :=
    ((lipschitzWith_tanh_response.continuous.measurable).comp (hG.const_add z)).pow_const 2
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_of_lt (Real.tanh_sq_lt_one _)

lemma variance_le_cosh_sq_mul_tanh_shift_integral
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta)
    {z : ℝ} (hz : |z| ≤ beta + 1) :
    variance G μ ≤ Real.cosh (2 * beta + 1) ^ 2 *
      ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have hGI : MemLp G 2 μ :=
    MemLp.of_bound hG.aestronglyMeasurable beta (by simpa only [Real.norm_eq_abs] using hBound)
  have hshiftI : Integrable (fun w => (z + G w) ^ 2) μ :=
    ((memLp_const z).add hGI).integrable_sq
  have htanI := integrable_tanh_shift_sq (μ := μ) hG z
  calc
    variance G μ = variance (fun w => z + G w) μ :=
      (variance_const_add hG.aestronglyMeasurable z).symm
    _ ≤ ∫ w, (z + G w) ^ 2 ∂μ :=
      variance_le_expectation_sq (hG.const_add z).aestronglyMeasurable
    _ ≤ ∫ w, Real.cosh (2 * beta + 1) ^ 2 * Real.tanh (z + G w) ^ 2 ∂μ := by
      apply integral_mono_ae hshiftI (htanI.const_mul _)
      filter_upwards [hBound] with w hw
      apply sq_le_cosh_sq_mul_tanh_sq
      calc
        |z + G w| ≤ |z| + |G w| := abs_add_le _ _
        _ ≤ (beta + 1) + beta := add_le_add hz hw
        _ = 2 * beta + 1 := by ring
    _ = Real.cosh (2 * beta + 1) ^ 2 *
        ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := integral_const_mul _ _

lemma variance_le_beta_sq_of_abs_le
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) :
    variance G μ ≤ beta ^ 2 := by
  have h := variance_le_sq_of_bounded (hBound.mono fun _ hw => abs_le.mp hw)
    hG.aemeasurable
  convert! h using 1
  ring

lemma variance_le_tanh_shift_integral_of_far
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta)
    {z : ℝ} (hz : beta + 1 < |z|) :
    variance G μ ≤ (beta ^ 2 / Real.tanh 1 ^ 2) *
      ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have htpos : 0 < Real.tanh 1 ^ 2 := sq_pos_of_pos tanh_one_pos_response
  have htanI := integrable_tanh_shift_sq (μ := μ) hG z
  have hlow : Real.tanh 1 ^ 2 ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
    calc
      Real.tanh 1 ^ 2 = ∫ _w : Ω, Real.tanh 1 ^ 2 ∂μ := by simp
      _ ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
        apply integral_mono_ae (integrable_const _) htanI
        filter_upwards [hBound] with w hw
        apply tanh_one_sq_le_of_one_le_abs
        have htri : |z| ≤ |z + G w| + |G w| := by
          calc
            |z| = |(z + G w) + (-G w)| := by congr 1; ring
            _ ≤ |z + G w| + |-G w| := abs_add_le _ _
            _ = |z + G w| + |G w| := by rw [abs_neg]
        linarith
  calc
    variance G μ ≤ beta ^ 2 := variance_le_beta_sq_of_abs_le hG hBound
    _ = (beta ^ 2 / Real.tanh 1 ^ 2) * Real.tanh 1 ^ 2 := by
      rw [div_mul_cancel₀ _ (ne_of_gt htpos)]
    _ ≤ (beta ^ 2 / Real.tanh 1 ^ 2) *
        ∫ w, Real.tanh (z + G w) ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left hlow (div_nonneg (sq_nonneg _) (le_of_lt htpos))

lemma variance_le_uniform_tanh_shift_integral
    (hG : Measurable G) (hBound : ∀ᵐ w ∂μ, |G w| ≤ beta) (z : ℝ) :
    variance G μ ≤ (Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2) *
      ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have hnonneg : 0 ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases hz : |z| ≤ beta + 1
  · exact (variance_le_cosh_sq_mul_tanh_shift_integral hG hBound hz).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hnonneg)
  · exact (variance_le_tanh_shift_integral_of_far hG hBound (lt_of_not_ge hz)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) hnonneg)

lemma exists_pos_uniform_shifted_tanh_variance (beta : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : Ω → ℝ), Measurable G →
      (∀ᵐ w ∂μ, |G w| ≤ beta) → ∀ z : ℝ,
      c * variance G μ ≤ ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  let C : ℝ := Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2
  have hC : 0 < C := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro G hG hBound z
  have h := variance_le_uniform_tanh_shift_integral hG hBound z
  calc
    C⁻¹ * variance G μ ≤ C⁻¹ * (C * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hC))
    _ = ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC), one_mul]

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

lemma integral_responseAttenuation_shift_sq_le {theta z : ℝ}
    (hθ : theta ^ 2 ≤ 1) (hG : Measurable G) :
    (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
      1 - (1 - theta ^ 2) * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
  have hm : Measurable (fun w => responseAttenuation theta (z + G w) ^ 2) :=
    ((continuous_responseAttenuation hθ).measurable.comp (hG.const_add z)).pow_const 2
  have ha_le : ∀ w, responseAttenuation theta (z + G w) ^ 2 ≤
      responseAttenuation theta (z + G w) := by
    intro w
    have hp := responseAttenuation_pos hθ (z + G w)
    have hle := responseAttenuation_le_one hθ (z + G w)
    nlinarith
  have hInt : Integrable (fun w => responseAttenuation theta (z + G w) ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (ha_le w).trans (responseAttenuation_le_one hθ (z + G w))
  calc
    (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤
        ∫ w, 1 - (1 - theta ^ 2) * Real.tanh (z + G w) ^ 2 ∂μ := by
      apply integral_mono hInt
        ((integrable_const _).sub ((integrable_tanh_shift_sq hG z).const_mul _))
      intro w
      exact (ha_le w).trans (responseAttenuation_le_one_sub hθ (z + G w))
    _ = 1 - (1 - theta ^ 2) * ∫ w, Real.tanh (z + G w) ^ 2 ∂μ := by
      rw [integral_sub (integrable_const _)
        ((integrable_tanh_shift_sq hG z).const_mul _), integral_const_mul]
      simp

lemma exists_pos_uniform_shifted_attenuation_loss {theta : ℝ} (hθ : theta ^ 2 < 1)
    (beta : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : Ω → ℝ), Measurable G →
      (∀ᵐ w ∂μ, |G w| ≤ beta) → ∀ z : ℝ,
      (∫ w, responseAttenuation theta (z + G w) ^ 2 ∂μ) ≤ 1 - c * variance G μ := by
  obtain ⟨c, hc, hcomp⟩ := exists_pos_uniform_shifted_tanh_variance (μ := μ) beta
  refine ⟨(1 - theta ^ 2) * c, mul_pos (sub_pos.mpr hθ) hc, ?_⟩
  intro G hG hBound z
  have h := mul_le_mul_of_nonneg_left (hcomp G hG hBound z)
    (sub_nonneg.mpr (le_of_lt hθ))
  have hi := integral_responseAttenuation_shift_sq_le (μ := μ) (le_of_lt hθ) hG (z := z)
  nlinarith

end Probability

end Problem367

end

end OAI
