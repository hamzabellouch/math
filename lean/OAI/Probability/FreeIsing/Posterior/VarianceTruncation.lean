import OAI.Probability.FreeIsing.Posterior.VarianceTimeIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace Problem367

theorem sq_sub_min_le_fourth_div_sq {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) :
    (a - min a R) ^ 2 ≤ a ^ 4 / R ^ 2 := by
  by_cases h : a ≤ R
  · rw [min_eq_left h, sub_self, zero_pow (by decide)]
    positivity
  · have hRa : R ≤ a := (lt_of_not_ge h).le
    rw [min_eq_right hRa]
    have hsmall : (a - R) ^ 2 ≤ a ^ 2 := by nlinarith
    apply hsmall.trans
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    have hs : R ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hR.le ha).mpr hRa
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg a)]

theorem integral_sq_sub_min_le_fourth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : Ω → ℝ}
    (hA : Measurable A) (hpos : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    (hfour : Integrable (fun ω => A ω ^ 4) μ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun ω => (A ω - min (A ω) R) ^ 2) μ ∧
      (∫ ω, (A ω - min (A ω) R) ^ 2 ∂μ) ≤ (∫ ω, A ω ^ 4 ∂μ) / R ^ 2 := by
  have hb : ∀ᵐ ω ∂μ, (A ω - min (A ω) R) ^ 2 ≤ A ω ^ 4 / R ^ 2 :=
    hpos.mono (fun ω hω => sq_sub_min_le_fourth_div_sq hω hR)
  have hi : Integrable (fun ω => (A ω - min (A ω) R) ^ 2) μ := by
    apply (hfour.div_const (R ^ 2)).mono' (by fun_prop)
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hω
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, A ω ^ 4 / R ^ 2 ∂μ := integral_mono_ae hi (hfour.div_const _) hb
    _ = _ := by rw [integral_div]

theorem tendsto_integral_sq_sub_min_of_fourth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : Ω → ℝ}
    (hA : Measurable A) (hpos : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    (hfour : Integrable (fun ω => A ω ^ 4) μ) :
    Tendsto (fun n : ℕ => ∫ ω, (A ω - min (A ω) ((n : ℝ) + 1)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (∫ ω, A ω ^ 4 ∂μ) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
    simpa [div_pow, div_eq_mul_inv] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul
        (∫ ω, A ω ^ 4 ∂μ)
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun _ => (integral_sq_sub_min_le_fourth hA hpos hfour (by positivity)).2) ht

def inverseVarianceCap (R m : ℝ) : ℝ := min ((1 - m ^ 2)⁻¹) R

theorem measurable_inverseVarianceCap (R : ℝ) : Measurable (inverseVarianceCap R) := by
  unfold inverseVarianceCap
  fun_prop

theorem inverseVarianceCap_bounds {R m : ℝ} (hR : 0 ≤ R) (hm : |m| ≤ 1) :
    0 ≤ inverseVarianceCap R m ∧ inverseVarianceCap R m ≤ R := by
  refine ⟨le_min ?_ hR, min_le_right _ _⟩
  exact inv_nonneg.mpr (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hm))

theorem isStronglyProgressive_inverseVarianceCap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m) (R : ℝ) :
    IsStronglyProgressive F (fun t ω => inverseVarianceCap R (m t ω)) := by
  intro t
  exact ((measurable_inverseVarianceCap R).comp (hm t).measurable).stronglyMeasurable

theorem HasFreeIsingLaw.brownian_inverse_variance_truncation_error
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω))
    (T : ℝ≥0) (v : TreeVertex d) {R : ℝ} (hR : 0 < R) :
    let m := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      infiniteGibbsSpinMean beta v (fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) +
        B i p.1.toNNReal (p.2.2 i))
    let E := fun p => ((1 - m p ^ 2)⁻¹ - inverseVarianceCap R (m p)) ^ 2
    let ρ := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    Integrable E ρ ∧ (∫ p, E p ∂ρ) ≤
      ((T : ℝ) * (2 * Real.exp (8 * ((d : ℝ) * beta + T) + (T : ℝ) * 8 ^ 2 / 2))) /
        R ^ 2 := by
  have hm := measurable_brownian_gibbs_posterior_real_time beta v B hmB hcB
  have hpos : ∀ p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
      0 ≤ (1 - (infiniteGibbsSpinMean beta v (fun i =>
        (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) + B i p.1.toNNReal (p.2.2 i))) ^ 2)⁻¹ := by
    intro p
    exact inv_nonneg.mpr (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr
      (infiniteGibbsSpinMean_abs_le_one beta v _)))
  have hfour := hμ.brownian_gibbs_posterior_inverse_variance_time_moment
    hbeta ν hB hmB hcB T v 4
  have h := integral_sq_sub_min_le_fourth (((hm.pow_const 2).const_sub 1).inv)
    (ae_of_all _ hpos) hfour.1 hR
  refine ⟨h.1, h.2.trans ?_⟩
  convert (div_le_div_of_nonneg_right hfour.2 (sq_nonneg R)) using 1
  norm_num

theorem HasFreeIsingLaw.tendsto_brownian_inverse_variance_truncation
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i ω, Continuous (fun t => B i t ω))
    (T : ℝ≥0) (v : TreeVertex d) :
    let m := fun p : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      infiniteGibbsSpinMean beta v (fun i => (p.1.toNNReal : ℝ) * spinSign (p.2.1 i) +
        B i p.1.toNNReal (p.2.2 i))
    let ρ := (volume.restrict (Ioc (0 : ℝ) T)).prod (μ.prod (Measure.infinitePi ν))
    Tendsto (fun n : ℕ => ∫ p,
      ((1 - m p ^ 2)⁻¹ - inverseVarianceCap ((n : ℝ) + 1) (m p)) ^ 2 ∂ρ)
      atTop (𝓝 0) := by
  have hm := measurable_brownian_gibbs_posterior_real_time beta v B hmB hcB
  apply tendsto_integral_sq_sub_min_of_fourth (((hm.pow_const 2).const_sub 1).inv)
  · apply ae_of_all
    intro p
    exact inv_nonneg.mpr (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr
      (infiniteGibbsSpinMean_abs_le_one beta v _)))
  · exact (hμ.brownian_gibbs_posterior_inverse_variance_time_moment
      hbeta ν hB hmB hcB T v 4).1

end Problem367

end

end OAI
