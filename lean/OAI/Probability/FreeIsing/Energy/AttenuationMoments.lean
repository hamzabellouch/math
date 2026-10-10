import OAI.Probability.FreeIsing.Energy.Attenuation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma log_responseAttenuation_sub_sq_le {theta x y : ℝ} (hθ : theta ^ 2 ≤ 1) :
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)) ^ 2 ≤
      4 * (x - y) ^ 2 := by
  have h := (lipschitzWith_log_responseAttenuation hθ).dist_le_mul x y
  have ha : |Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)| ≤
      2 * |x - y| := by simpa [Real.dist_eq] using h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (abs_nonneg (x - y)))).mpr ha
  norm_num [mul_pow, sq_abs] at hs ⊢
  exact hs

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {Y Y' : Ω → ℝ}

lemma integrable_log_responseAttenuation_sub_sq
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ) :
    Integrable (fun w =>
      (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2) μ := by
  have hm : Measurable (fun x => Real.log (responseAttenuation theta x)) :=
    (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  apply (hInt.const_mul 4).mono'
    (((hm.comp hY).sub (hm.comp hY')).pow_const 2).aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_responseAttenuation_sub_sq_le hθ

lemma integral_log_responseAttenuation_sub_sq_le [IsProbabilityMeasure μ]
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ)
    {R H V B : ℝ} (hH : 0 ≤ H)
    (hBound : ∀ᵐ w ∂μ, |Y w - Y' w| ≤ H)
    (hVar : (∫ w, (Y w - Y' w) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {w | ¬ (|Y w| ≤ R ∧ |Y' w| ≤ R)} ≤ B) :
    (∫ w, (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2 ∂μ) ≤
      4 * R ^ 2 * V + min (4 * V) (4 * H ^ 2 * B) := by
  let D : Ω → ℝ := fun w =>
    (Real.log (responseAttenuation theta (Y w)) -
      Real.log (responseAttenuation theta (Y' w))) ^ 2
  let E : Ω → ℝ := fun w => (Y w - Y' w) ^ 2
  let G : Set Ω := {w | |Y w| ≤ R ∧ |Y' w| ≤ R}
  have hG : MeasurableSet G :=
    (measurableSet_le hY.abs measurable_const).inter
      (measurableSet_le hY'.abs measurable_const)
  have hDI : Integrable D μ := integrable_log_responseAttenuation_sub_sq hθ hY hY' hInt
  have hEI : Integrable E μ := hInt
  have hD_nonneg : ∀ w, 0 ≤ D w := fun w => sq_nonneg _
  have hE_nonneg : ∀ w, 0 ≤ E w := fun w => sq_nonneg _
  have hglobal : ∀ w, D w ≤ 4 * E w := fun w => log_responseAttenuation_sub_sq_le hθ
  have hglobal_int : (∫ w, D w ∂μ) ≤ 4 * V := by
    calc
      (∫ w, D w ∂μ) ≤ ∫ w, 4 * E w ∂μ :=
        integral_mono hDI (hEI.const_mul 4) hglobal
      _ = 4 * ∫ w, E w ∂μ := integral_const_mul _ _
      _ ≤ 4 * V := mul_le_mul_of_nonneg_left hVar (by norm_num)
  have hgood : (∫ w in G, D w ∂μ) ≤ 4 * R ^ 2 * V := by
    calc
      (∫ w in G, D w ∂μ) ≤ ∫ w in G, (4 * R ^ 2) * E w ∂μ := by
        apply setIntegral_mono_on hDI.integrableOn ((hEI.const_mul _).integrableOn) hG
        intro w hw
        exact log_responseAttenuation_small_field_sq hθ hw.1 hw.2
      _ = (4 * R ^ 2) * ∫ w in G, E w ∂μ := integral_const_mul _ _
      _ ≤ (4 * R ^ 2) * ∫ w, E w ∂μ :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hEI (Filter.Eventually.of_forall hE_nonneg))
          (by positivity)
      _ ≤ 4 * R ^ 2 * V := mul_le_mul_of_nonneg_left hVar (by positivity)
  have hbad_var : (∫ w in Gᶜ, D w ∂μ) ≤ 4 * V := by
    exact (setIntegral_le_integral hDI (Filter.Eventually.of_forall hD_nonneg)).trans hglobal_int
  have hbad_tail : (∫ w in Gᶜ, D w ∂μ) ≤ 4 * H ^ 2 * B := by
    calc
      (∫ w in Gᶜ, D w ∂μ) ≤ ∫ _w in Gᶜ, 4 * H ^ 2 ∂μ := by
        apply setIntegral_mono_ae hDI.integrableOn (integrable_const _).integrableOn
        filter_upwards [hBound] with w hw
        have hs : E w ≤ H ^ 2 := by
          have h := (sq_le_sq₀ (abs_nonneg _) hH).mpr hw
          simpa [E, sq_abs] using h
        exact (hglobal w).trans (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = 4 * H ^ 2 * μ.real Gᶜ := by rw [setIntegral_const]; simp [mul_comm]
      _ ≤ 4 * H ^ 2 * B := mul_le_mul_of_nonneg_left hTail (by positivity)
  have hsplit := integral_add_compl hG hDI
  change (∫ w, D w ∂μ) ≤ _
  rw [← hsplit]
  exact add_le_add hgood (le_min hbad_var hbad_tail)

lemma measureReal_bad_field_le [IsFiniteMeasure μ] {R B₁ B₂ : ℝ}
    (hTail : μ.real {w | R < |Y w|} ≤ B₁)
    (hTail' : μ.real {w | R < |Y' w|} ≤ B₂) :
    μ.real {w | ¬ (|Y w| ≤ R ∧ |Y' w| ≤ R)} ≤ B₁ + B₂ := by
  have hset : {w | ¬ (|Y w| ≤ R ∧ |Y' w| ≤ R)} =
      {w | R < |Y w|} ∪ {w | R < |Y' w|} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or, not_le]
  rw [hset]
  exact (measureReal_union_le _ _).trans (add_le_add hTail hTail')

lemma integral_log_responseAttenuation_sub_sq_le_of_marginal_tails
    [IsProbabilityMeasure μ]
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ)
    {R H V B₁ B₂ : ℝ} (hH : 0 ≤ H)
    (hBound : ∀ᵐ w ∂μ, |Y w - Y' w| ≤ H)
    (hVar : (∫ w, (Y w - Y' w) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {w | R < |Y w|} ≤ B₁)
    (hTail' : μ.real {w | R < |Y' w|} ≤ B₂) :
    (∫ w, (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2 ∂μ) ≤
      4 * R ^ 2 * V + min (4 * V) (4 * H ^ 2 * (B₁ + B₂)) := by
  exact integral_log_responseAttenuation_sub_sq_le hθ hY hY' hInt hH
    hBound hVar (measureReal_bad_field_le hTail hTail')

end Probability

end Problem367

end

end OAI
