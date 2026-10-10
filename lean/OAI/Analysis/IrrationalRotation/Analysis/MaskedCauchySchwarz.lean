import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace InvariantProjection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_mul_le_sqrt_sq_mul_sqrt_sq {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) :
    (∫ ω, f ω * g ω ∂μ) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hf_nonneg hg_nonneg (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

theorem integral_mul_le_sqrt_of_sq_integral_le {f g : Ω → ℝ} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf_sq : (∫ ω, f ω ^ 2 ∂μ) ≤ δ)
    (hg_sq : (∫ ω, g ω ^ 2 ∂μ) ≤ 1) :
    (∫ ω, f ω * g ω ∂μ) ≤ Real.sqrt δ := by
  calc
    (∫ ω, f ω * g ω ∂μ) ≤
        Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) :=
      integral_mul_le_sqrt_sq_mul_sqrt_sq hf hg hf_nonneg hg_nonneg
    _ ≤ Real.sqrt δ * Real.sqrt 1 :=
      mul_le_mul (Real.sqrt_le_sqrt hf_sq) (Real.sqrt_le_sqrt hg_sq)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt δ := by simp

theorem integral_indicator_le_of_condExp_indicator_le
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {H : Set Ω} (hH : MeasurableSet[mΩ] H)
    {w : Ω → ℝ} {δ : ℝ} (hw : Integrable w μ)
    (hwm : StronglyMeasurable[m] w) (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hcond : μ[H.indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    (∫ ω, H.indicator w ω ∂μ) ≤ δ * ∫ ω, w ω ∂μ := by
  have hmul : w * H.indicator (fun _ => (1 : ℝ)) = H.indicator w := by
    funext ω
    by_cases hω : ω ∈ H <;> simp [hω]
  have hpull := condExp_mul_of_stronglyMeasurable_left hwm
    (show Integrable (w * H.indicator (fun _ => (1 : ℝ))) μ by
      rw [hmul]
      exact hw.indicator hH)
    ((integrable_const (1 : ℝ)).indicator hH)
  have hprod : Integrable (w * μ[H.indicator (fun _ => (1 : ℝ)) | m]) μ :=
    integrable_condExp.congr hpull
  calc
    (∫ ω, H.indicator w ω ∂μ) =
        ∫ ω, μ[w * H.indicator (fun _ => (1 : ℝ)) | m] ω ∂μ := by
      rw [integral_condExp hm, hmul]
    _ = ∫ ω, w ω * μ[H.indicator (fun _ => (1 : ℝ)) | m] ω ∂μ :=
      integral_congr_ae hpull
    _ ≤ ∫ ω, δ * w ω ∂μ := by
      apply integral_mono_ae hprod (hw.const_mul δ)
      filter_upwards [hcond, hw_nonneg] with ω hω hwω
      simpa only [Pi.mul_apply, mul_comm] using mul_le_mul_of_nonneg_left hω hwω
    _ = δ * ∫ ω, w ω ∂μ := integral_const_mul δ w

theorem lintegral_tsum_indicator_le_of_condExp_indicator_le
    {ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {H : ι → Set Ω} (hH : ∀ i, MeasurableSet[mΩ] (H i))
    {w : ι → Ω → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, Integrable (w i) μ)
    (hwm : ∀ i, StronglyMeasurable[m] (w i))
    (hw_nonneg : ∀ i, 0 ≤ᵐ[μ] w i)
    (hcond : ∀ i, μ[(H i).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator (w i) ω) ∂μ) ≤
      ENNReal.ofReal δ * ∫⁻ ω, ∑' i, ENNReal.ofReal (w i ω) ∂μ := by
  rw [lintegral_tsum (fun i => ((hw i).indicator (hH i)).aemeasurable.ennreal_ofReal),
    lintegral_tsum (fun i => (hw i).aemeasurable.ennreal_ofReal),
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  have hmask_nonneg : 0 ≤ᵐ[μ] (H i).indicator (w i) := by
    filter_upwards [hw_nonneg i] with ω hω
    by_cases hi : ω ∈ H i
    · simpa only [Set.indicator_of_mem hi, Pi.zero_apply] using hω
    · simp [hi]
  rw [← ofReal_integral_eq_lintegral_ofReal ((hw i).indicator (hH i)) hmask_nonneg,
    ← ofReal_integral_eq_lintegral_ofReal (hw i) (hw_nonneg i),
    ← ENNReal.ofReal_mul hδ]
  exact ENNReal.ofReal_le_ofReal
    (integral_indicator_le_of_condExp_indicator_le (mΩ := mΩ) hm (hH i) (hw i) (hwm i)
      (hw_nonneg i) (hcond i))

theorem lintegral_tsum_indicator_le_of_condExp_indicator_le_of_energy_le_one
    {ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {H : ι → Set Ω} (hH : ∀ i, MeasurableSet[mΩ] (H i))
    {w : ι → Ω → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, Integrable (w i) μ)
    (hwm : ∀ i, StronglyMeasurable[m] (w i))
    (hw_nonneg : ∀ i, 0 ≤ᵐ[μ] w i)
    (hcond : ∀ i, μ[(H i).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ)
    (henergy : (∫⁻ ω, ∑' i, ENNReal.ofReal (w i ω) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator (w i) ω) ∂μ) ≤
      ENNReal.ofReal δ := by
  calc
    _ ≤ ENNReal.ofReal δ * ∫⁻ ω, ∑' i, ENNReal.ofReal (w i ω) ∂μ :=
      lintegral_tsum_indicator_le_of_condExp_indicator_le (mΩ := mΩ) hm hH hδ hw hwm hw_nonneg hcond
    _ ≤ ENNReal.ofReal δ * 1 := mul_le_mul_right henergy _
    _ = ENNReal.ofReal δ := mul_one _

end InvariantProjection

end OAI
