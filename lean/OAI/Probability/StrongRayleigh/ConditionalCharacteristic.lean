import Mathlib

namespace OAI

universe u_1

noncomputable section

open MeasureTheory Filter

namespace Problem336AdditiveD139.ConditionalCharacteristic

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}

theorem integral_mul_condExp (hm : m ≤ mΩ) {f g : Ω → ℂ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) :
    (∫ ω, f ω * g ω ∂μ) = ∫ ω, f ω * μ[g | m] ω ∂μ := by
  have hp := condExp_stronglyMeasurable_bilin_of_bound
    (ContinuousLinearMap.mul ℝ ℂ) hm hf hg 1 hbound
  calc
    _ = ∫ ω, μ[fun a => f a * g a | m] ω ∂μ := (integral_condExp hm).symm
    _ = _ := integral_congr_ae hp

theorem integral_mul_error_le (hm : m ≤ mΩ) {f g : Ω → ℂ}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) {a : ℂ} {ε : ℝ}
    (herror : ∀ᵐ ω ∂μ, ‖μ[g | m] ω - a‖ ≤ ε) :
    ‖(∫ ω, f ω * g ω ∂μ) - a * (∫ ω, f ω ∂μ)‖ ≤ ε := by
  have hfint : Integrable f μ := (integrable_const (1 : ℝ)).mono'
    (hf.mono hm).aestronglyMeasurable hbound
  have hfg : Integrable (fun ω => f ω * μ[g | m] ω) μ :=
    integrable_condExp.bdd_mul (hf.mono hm).aestronglyMeasurable hbound
  have heq : (∫ ω, f ω * g ω ∂μ) - a * (∫ ω, f ω ∂μ) =
      ∫ ω, f ω * (μ[g | m] ω - a) ∂μ := by
    rw [integral_mul_condExp hm hf hg hbound]
    calc
      _ = (∫ ω, f ω * μ[g | m] ω ∂μ) - ∫ ω, f ω * a ∂μ := by
        rw [integral_mul_const]
        ring
      _ = ∫ ω, f ω * μ[g | m] ω - f ω * a ∂μ :=
        (integral_sub hfg (hfint.mul_const a)).symm
      _ = _ := by congr 1; funext ω; ring
  rw [heq]
  have hb : ∀ᵐ ω ∂μ, ‖f ω * (μ[g | m] ω - a)‖ ≤ ε := by
    filter_upwards [hbound, herror] with ω hfω heω
    rw [norm_mul]
    calc
      _ ≤ 1 * ε := mul_le_mul hfω heω (norm_nonneg _) (by norm_num)
      _ = ε := one_mul ε
  simpa using norm_integral_le_of_norm_le_const hb

end Problem336AdditiveD139.ConditionalCharacteristic

end

end OAI
