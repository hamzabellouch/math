import OAI.Probability.FreeIsing.Conditioning.FiniteEntropySmallTime
import OAI.Probability.FreeIsing.Posterior.FieldMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

def selectedGaussianField {d : ℕ} {ι : Type*}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  fun p => Real.artanh (selectedPosterior
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (fun s z => (t : ℝ) * spinSign s + z) v r p)

theorem measurable_selectedGaussianField {d : ℕ} {ι : Type*}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedGaussianField μ t v r) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  apply ha.comp
  apply measurable_selectedPosterior
  exact ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
    measurable_snd

theorem HasFreeIsingLaw.integrable_selectedGaussianField_abs_pow
    {d : ℕ} {ι : Type*} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) (p : ℕ) :
    Integrable (fun q => |selectedGaussianField μ t v r q| ^ p)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply integrable_abs_pow_of_bounded_perturbation p
    (show 0 ≤ (d : ℝ) * beta + t by positivity)
    (measurable_selectedGaussianField μ t v r).aemeasurable
    (integrable_abs_pow_of_gaussianLaw (gaussianPlanted_noise_hasLaw μ t r) p)
  filter_upwards [hμ.selected_gaussian_posterior_field_bound hb t v r hr] with q hq
  have hs : |(t : ℝ) * spinSign (q.1 r)| = t := by
    cases he : q.1 r <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  calc
    |selectedGaussianField μ t v r q - q.2 r| =
        |(selectedGaussianField μ t v r q - observation t q r) +
          (t : ℝ) * spinSign (q.1 r)| := by
      congr 1
      simp only [observation]
      ring
    _ ≤ |selectedGaussianField μ t v r q - observation t q r| +
        |(t : ℝ) * spinSign (q.1 r)| := abs_add_le _ _
    _ ≤ (d : ℝ) * beta + t := by
      rw [hs]
      exact add_le_add hq.2 le_rfl

theorem HasFreeIsingLaw.selectedGaussianField_secondMoment_le_information
    {d : ℕ} {ι : Type*} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (v : ι → TreeVertex d)
    (r : TreeVertex d) (hr : r ∈ Set.range v) :
    (∫ q, (selectedGaussianField μ t v r q) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.cosh ((d : ℝ) * beta + 1) ^ 2 *
        (∫ q, (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (fun s z => (t : ℝ) * spinSign s + z) v r q) ^ 2
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) +
      (16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32)) * (t : ℝ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let S := fun q : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    spinSign (q.1 r)
  have hS : Measurable S := PlantedInformation.measurable_spinSign.comp
    ((measurable_pi_apply r).comp measurable_fst)
  have hSb : ∀ᵐ q ∂P, |S q| ≤ 1 := Eventually.of_forall fun q => by
    cases he : q.1 r <;> simp [S, he, spinSign]
  have hX4 := gaussian_channel_fourth_moment hS.aemeasurable hSb
    (gaussianPlanted_noise_hasLaw μ t r) ht
  have hfield := hμ.selected_gaussian_posterior_field_bound hb t v r hr
  have hsecond := integral_sq_le_tanh_sq_add_fourth
    (show 0 ≤ (d : ℝ) * beta by positivity)
    (measurable_selectedGaussianField μ t v r).aemeasurable hX4.1
    (hfield.mono fun q hq => hq.2)
  have htanh : (fun q => Real.tanh (selectedGaussianField μ t v r q) ^ 2) =ᵐ[P]
      fun q => (selectedPosterior P
        (fun s z => (t : ℝ) * spinSign s + z) v r q) ^ 2 := by
    filter_upwards [hfield] with q hq
    rw [selectedGaussianField, Real.tanh_artanh hq.1]
  rw [integral_congr_ae htanh] at hsecond
  apply hsecond.2.trans
  have hfourth := mul_le_mul_of_nonneg_left hX4.2
    (show 0 ≤ 2 * (1 + ((d : ℝ) * beta) ^ 2) by positivity)
  dsimp only [S] at hfourth
  nlinarith

def criticalComponentFieldMomentConstant (d : ℕ) (beta : ℝ) : ℝ :=
  Real.cosh ((d : ℝ) * beta + 1) ^ 2 *
    Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4)) +
    16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32)

theorem criticalComponentFieldMomentConstant_pos (d : ℕ) (beta : ℝ) :
    0 < criticalComponentFieldMomentConstant d beta := by
  unfold criticalComponentFieldMomentConstant
  positivity

theorem HasFreeIsingLaw.gaussianComponentField_critical_secondMoment
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d) :
    (∫ q, (selectedGaussianField μ t (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c) q) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      criticalComponentFieldMomentConstant d beta * Real.sqrt (t : ℝ) := by
  have hr : RootedBroadcast.branchRoot c ∈
      Set.range (componentIndexVertex (c := c)) := by
    apply mem_range_componentIndexVertex.mpr
    exact ⟨[], by simp [RootedBroadcast.branchRoot]⟩
  have hsecond := hμ.selectedGaussianField_secondMoment_le_information hb t ht
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) hr
  have hinfo := hμ.gaussian_component_critical_information_upper hd hb hcritical t ht c
  change gaussianComponentInformation μ t c ≤ _ at hinfo
  change _ ≤ Real.cosh ((d : ℝ) * beta + 1) ^ 2 *
    gaussianComponentInformation μ t c + _ at hsecond
  have hi := mul_le_mul_of_nonneg_left hinfo
    (sq_nonneg (Real.cosh ((d : ℝ) * beta + 1)))
  have htime := mul_le_mul_of_nonneg_left (Real.le_sqrt_self_iff.mpr ht)
    (show 0 ≤ 16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32) by positivity)
  unfold criticalComponentFieldMomentConstant
  nlinarith

theorem HasFreeIsingLaw.gaussianComponentField_critical_firstMoment
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d) :
    (∫ q, |selectedGaussianField μ t (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c) q|
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.sqrt (criticalComponentFieldMomentConstant d beta) *
        (t : ℝ) ^ (1 / 4 : ℝ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hr : RootedBroadcast.branchRoot c ∈
      Set.range (componentIndexVertex (c := c)) := by
    apply mem_range_componentIndexVertex.mpr
    exact ⟨[], by simp [RootedBroadcast.branchRoot]⟩
  have hint := hμ.integrable_selectedGaussianField_abs_pow hb t
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) hr 2
  simp only [sq_abs] at hint
  have hfirst := integral_abs_le_sqrt_integral_sq
    (measurable_selectedGaussianField μ t (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)).aemeasurable hint
  have hsecond := hμ.gaussianComponentField_critical_secondMoment hd hb hcritical t ht c
  have hquarter : Real.sqrt (Real.sqrt (t : ℝ)) = (t : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul t.coe_nonneg]
    congr 1
    norm_num
  apply hfirst.trans ((Real.sqrt_le_sqrt hsecond).trans_eq ?_)
  rw [Real.sqrt_mul (criticalComponentFieldMomentConstant_pos d beta).le, hquarter]

def criticalComponentBaseExponent (d : ℕ) (beta : ℝ) : ℝ :=
  2 + criticalComponentFieldMomentConstant d beta +
    Real.sqrt (criticalComponentFieldMomentConstant d beta)

theorem criticalComponentBaseExponent_ge_two (d : ℕ) (beta : ℝ) :
    2 ≤ criticalComponentBaseExponent d beta := by
  unfold criticalComponentBaseExponent
  linarith [criticalComponentFieldMomentConstant_pos d beta,
    Real.sqrt_nonneg (criticalComponentFieldMomentConstant d beta)]

theorem HasFreeIsingLaw.gaussianComponentField_critical_base_moments
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d)
    (p : ℕ) (hp : p < 3) :
    (∫ q, |selectedGaussianField μ t (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c) q| ^ p
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (criticalComponentBaseExponent d beta * (p : ℝ) ^ 2) *
        (t : ℝ) ^ ((p : ℝ) / 4) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hD := criticalComponentFieldMomentConstant_pos d beta
  have hS := Real.sqrt_nonneg (criticalComponentFieldMomentConstant d beta)
  interval_cases p
  · simp
  · have hfirst := hμ.gaussianComponentField_critical_firstMoment hd hb hcritical t ht c
    norm_num only [Nat.cast_one, one_pow, pow_one, mul_one]
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg t.coe_nonneg _)
    have he := Real.add_one_le_exp (criticalComponentBaseExponent d beta)
    unfold criticalComponentBaseExponent at *
    linarith
  · have hsecond := hμ.gaussianComponentField_critical_secondMoment hd hb hcritical t ht c
    simp only [sq_abs]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.sqrt_eq_rpow]
    apply hsecond.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have he := Real.add_one_le_exp (criticalComponentBaseExponent d beta * (2 : ℝ) ^ 2)
    unfold criticalComponentBaseExponent at *
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at he
    nlinarith

end Problem367

end

end OAI
