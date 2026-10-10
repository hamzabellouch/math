import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.SquaredIntegralLp

theorem eLpNorm'_two_eq_lintegral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    eLpNorm' f 2 μ = (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm'_eq_lintegral_enorm]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [sq_abs]

theorem eLpNorm'_two_eq_ofReal_integral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ) :
    eLpNorm' f 2 μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm'_two_eq_lintegral_sq_rpow,
    ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun x => sq_nonneg (f x))]

theorem eLpNorm'_two_lt_ofReal_iff_integral_sq_lt
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ) {δ : ℝ} (hδ : 0 < δ) :
    eLpNorm' f 2 μ < ENNReal.ofReal δ ↔ (∫ x, f x ^ 2 ∂μ) < δ ^ 2 := by
  rw [eLpNorm'_two_eq_ofReal_integral_sq_rpow μ f hf, one_div,
    ENNReal.rpow_inv_lt_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two,
    ← ENNReal.ofReal_pow hδ.le]
  exact ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hδ)

theorem tendsto_eLpNorm'_two_of_lintegral_sq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : ℕ → X → ℝ) (g : Y → ℝ)
    (h : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x ^ 2) ∂μ) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂ν))) :
    Tendsto (fun n => eLpNorm' (f n) 2 μ) atTop (𝓝 (eLpNorm' g 2 ν)) := by
  simpa only [eLpNorm'_two_eq_lintegral_sq_rpow] using h.ennrpow_const (1 / 2 : ℝ)

theorem tendsto_eLpNorm'_two_of_integral_sq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : ℕ → X → ℝ) (g : Y → ℝ)
    (hf : ∀ n, Integrable (fun x => f n x ^ 2) μ)
    (hg : Integrable (fun y => g y ^ 2) ν)
    (h : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop
      (𝓝 (∫ y, g y ^ 2 ∂ν))) :
    Tendsto (fun n => eLpNorm' (f n) 2 μ) atTop (𝓝 (eLpNorm' g 2 ν)) := by
  have hreal := (ENNReal.continuous_ofReal.tendsto _).comp h
  have hp := hreal.ennrpow_const (1 / 2 : ℝ)
  simpa only [eLpNorm'_two_eq_ofReal_integral_sq_rpow μ _ (hf _),
    eLpNorm'_two_eq_ofReal_integral_sq_rpow ν _ hg, Function.comp_def] using hp

theorem eLpNorm_two_eq_lintegral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hfm]
  simpa only [ENNReal.toReal_ofNat] using eLpNorm'_two_eq_lintegral_sq_rpow μ f

theorem eLpNorm_two_eq_ofReal_integral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hfm : AEStronglyMeasurable f μ)
    (hf : Integrable (fun x => f x ^ 2) μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_two_eq_lintegral_sq_rpow μ f hfm,
    ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun x => sq_nonneg (f x))]

theorem eLpNorm_two_lt_ofReal_iff_integral_sq_lt
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hfm : AEStronglyMeasurable f μ)
    (hf : Integrable (fun x => f x ^ 2) μ) {δ : ℝ} (hδ : 0 < δ) :
    eLpNorm f 2 μ < ENNReal.ofReal δ ↔ (∫ x, f x ^ 2 ∂μ) < δ ^ 2 := by
  rw [eLpNorm_two_eq_ofReal_integral_sq_rpow μ f hfm hf, one_div,
    ENNReal.rpow_inv_lt_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two,
    ← ENNReal.ofReal_pow hδ.le]
  exact ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hδ)

theorem tendsto_eLpNorm_two_of_lintegral_sq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : ℕ → X → ℝ) (g : Y → ℝ)
    (hfm : ∀ index, AEStronglyMeasurable (f index) μ)
    (hgm : AEStronglyMeasurable g ν)
    (h : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x ^ 2) ∂μ) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (g y ^ 2) ∂ν))) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 (eLpNorm g 2 ν)) := by
  simpa only [eLpNorm_two_eq_lintegral_sq_rpow μ _ (hfm _),
    eLpNorm_two_eq_lintegral_sq_rpow ν _ hgm] using h.ennrpow_const (1 / 2 : ℝ)

theorem tendsto_eLpNorm_two_of_integral_sq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : ℕ → X → ℝ) (g : Y → ℝ)
    (hfm : ∀ index, AEStronglyMeasurable (f index) μ)
    (hgm : AEStronglyMeasurable g ν)
    (hf : ∀ n, Integrable (fun x => f n x ^ 2) μ)
    (hg : Integrable (fun y => g y ^ 2) ν)
    (h : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop
      (𝓝 (∫ y, g y ^ 2 ∂ν))) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 (eLpNorm g 2 ν)) := by
  have hreal := (ENNReal.continuous_ofReal.tendsto _).comp h
  have hp := hreal.ennrpow_const (1 / 2 : ℝ)
  simpa only [eLpNorm_two_eq_ofReal_integral_sq_rpow μ _ (hfm _) (hf _),
    eLpNorm_two_eq_ofReal_integral_sq_rpow ν _ hgm hg, Function.comp_def] using hp

end Invariant233.SquaredIntegralLp

end

end OAI
