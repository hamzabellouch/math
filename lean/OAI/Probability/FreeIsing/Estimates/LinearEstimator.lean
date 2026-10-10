import OAI.Probability.FreeIsing.Critical.Information

namespace OAI

open MeasureTheory
open scoped Topology ENNReal

namespace Problem367

section Estimator

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem integral_mul_sq_le_second_moments {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
      (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
  have hinner {u v : Ω → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ ω, u ω * v ω ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ω huω hvω
    simp [huω, hvω, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [hinner, pow_two] using h

theorem conditional_estimator_cauchy_schwarz [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {signal statistic : Ω → ℝ} (hsignal : MemLp signal 2 μ)
    (hstatistic : MemLp statistic 2 μ) (hadapted : StronglyMeasurable[m] statistic) :
    (∫ ω, signal ω * statistic ω ∂μ) ^ 2 ≤
      (∫ ω, (μ[signal | m] ω) ^ 2 ∂μ) * (∫ ω, statistic ω ^ 2 ∂μ) := by
  have hpost : MemLp (μ[signal | m]) 2 μ :=
    (memLp_congr_ae (hsignal.condExpL2_ae_eq_condExp (𝕜 := ℝ) hm)).mp
      (Lp.memLp ((condExpL2 ℝ ℝ hm (hsignal.toLp signal)).val))
  have heq : (∫ ω, signal ω * statistic ω ∂μ) =
      ∫ ω, μ[signal | m] ω * statistic ω ∂μ := by
    calc
      (∫ ω, signal ω * statistic ω ∂μ) = ∫ ω, μ[signal * statistic | m] ω ∂μ :=
        (integral_condExp hm).symm
      _ = ∫ ω, μ[signal | m] ω * statistic ω ∂μ := by
        apply integral_congr_ae
        exact condExp_mul_of_stronglyMeasurable_right hadapted
          (hsignal.integrable_mul hstatistic) (hsignal.integrable (by norm_num))
  rw [heq]
  exact integral_mul_sq_le_second_moments hpost hstatistic

theorem conditional_information_lower_of_estimator [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {signal statistic : Ω → ℝ} (hsignal : MemLp signal 2 μ)
    (hstatistic : MemLp statistic 2 μ) (hadapted : StronglyMeasurable[m] statistic)
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hcorrelation : (∫ ω, signal ω * statistic ω ∂μ) = t * a)
    (henergy : (∫ ω, statistic ω ^ 2 ∂μ) ≤ t * a + t ^ 2 * a ^ 3) :
    t * a / (1 + t * a ^ 2) ≤ ∫ ω, (μ[signal | m] ω) ^ 2 ∂μ := by
  let M : ℝ := ∫ ω, (μ[signal | m] ω) ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have hcs := conditional_estimator_cauchy_schwarz hm hsignal hstatistic hadapted
  rw [hcorrelation] at hcs
  have hbound : (t * a) ^ 2 ≤ M * (t * a + t ^ 2 * a ^ 3) :=
    hcs.trans (mul_le_mul_of_nonneg_left henergy hM)
  have hcancel : t * a ≤ M * (1 + t * a ^ 2) := by
    apply (mul_le_mul_iff_right₀ (mul_pos ht ha)).mp
    nlinarith only [hbound]
  apply (div_le_iff₀ (by positivity : 0 < 1 + t * a ^ 2)).mpr
  exact hcancel

theorem critical_information_of_estimators [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {signal : Ω → ℝ} (hsignal : MemLp signal 2 μ) (statistic : ℕ → Ω → ℝ)
    (hstatistic : ∀ n, MemLp (statistic n) 2 μ)
    (hadapted : ∀ n, StronglyMeasurable[m] (statistic n))
    {t : ℝ} (ht : 0 < t)
    (hcorrelation : ∀ n : ℕ, (∫ ω, signal ω * statistic n ω ∂μ) = t * ((n : ℝ) + 1))
    (henergy : ∀ n : ℕ, (∫ ω, statistic n ω ^ 2 ∂μ) ≤
      t * ((n : ℝ) + 1) + t ^ 2 * ((n : ℝ) + 1) ^ 3) :
    min (Real.sqrt t) 1 / 5 ≤ ∫ ω, (μ[signal | m] ω) ^ 2 ∂μ := by
  apply critical_information_lower_of_estimators ht
  intro n
  exact conditional_information_lower_of_estimator hm hsignal (hstatistic n)
    (hadapted n) ht (by positivity) (hcorrelation n) (henergy n)

end Estimator

section Monotonicity

variable {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem posterior_information_mono [IsFiniteMeasure μ]
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ mΩ) {signal : Ω → ℝ}
    (hsignal : MemLp signal 2 μ) :
    (∫ ω, (μ[signal | m₁] ω) ^ 2 ∂μ) ≤
      ∫ ω, (μ[signal | m₂] ω) ^ 2 ∂μ := by
  have hp : MemLp (μ[signal | m₂]) 2 μ := hsignal.condExp (by norm_num)
  have hi : Integrable (fun ω => ‖μ[signal | m₂] ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hp.integrable_sq
  have hc := integral_norm_condExp_rpow_le (m := m₁) (by norm_num : (1 : ℝ) ≤ 2) hi
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hc
  have heq : (∫ ω, (μ[μ[signal | m₂] | m₁] ω) ^ 2 ∂μ) =
      ∫ ω, (μ[signal | m₁] ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_condExp_of_le (f := signal) hm₁₂ hm₂] with ω hω
    rw [hω]
  rwa [heq] at hc

end Monotonicity

end Problem367

end OAI
