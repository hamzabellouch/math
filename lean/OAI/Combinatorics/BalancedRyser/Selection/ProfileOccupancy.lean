import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

namespace Balanced.PoissonProfile

open MeasureTheory

theorem not_ae_above_mean_with_margin
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℝ} {μ c ε : ℝ} (hf : Integrable f ν)
    (hmass : ν.real Set.univ = c) (hc : 0 < c) (hε : 0 < ε)
    (hmean : (∫ x, f x ∂ν) = μ * c) :
    ¬ (∀ᵐ x ∂ν, μ + ε ≤ f x) := by
  intro hhigh
  have h := integral_mono_ae (integrable_const (μ + ε)) hf hhigh
  simp only [integral_const, smul_eq_mul] at h
  rw [hmass, hmean] at h
  nlinarith [mul_pos hc hε]

theorem not_ae_below_mean_with_margin
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℝ} {μ c ε : ℝ} (hf : Integrable f ν)
    (hmass : ν.real Set.univ = c) (hc : 0 < c) (hε : 0 < ε)
    (hmean : (∫ x, f x ∂ν) = μ * c) :
    ¬ (∀ᵐ x ∂ν, f x ≤ μ - ε) := by
  intro hlow
  have h := integral_mono_ae hf (integrable_const (μ - ε)) hlow
  simp only [integral_const, smul_eq_mul] at h
  rw [hmass, hmean] at h
  nlinarith [mul_pos hc hε]

theorem no_common_sign_deviation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℝ} {μ c ε : ℝ} (hf : Integrable f ν)
    (hmass : ν.real Set.univ = c) (hc : 0 < c) (hε : 0 < ε)
    (hmean : (∫ x, f x ∂ν) = μ * c) :
    ¬ ((∀ᵐ x ∂ν, μ + ε ≤ f x) ∨ (∀ᵐ x ∂ν, f x ≤ μ - ε)) := by
  rintro (hhigh | hlow)
  · exact not_ae_above_mean_with_margin ν hf hmass hc hε hmean hhigh
  · exact not_ae_below_mean_with_margin ν hf hmass hc hε hmean hlow

end Balanced.PoissonProfile

end OAI
