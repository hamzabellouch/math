import Mathlib.MeasureTheory.Integral.Average

namespace OAI

/-! Elementary mean-oscillation bounds used for Sobolev square averages. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma average_mono_real {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    (⨍ x, f x ∂μ) ≤ ⨍ x, g x ∂μ := by
  rw [average_eq, average_eq]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg) (by positivity)

lemma abs_average_le_average_abs {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : |⨍ x, f x ∂μ| ≤ ⨍ x, |f x| ∂μ := by
  simpa only [average, Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (f := f) (μ := (μ univ)⁻¹ • μ))

lemma abs_sub_average_le_average_abs_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hf : Integrable f μ) (a : ℝ) :
    |a-(⨍ x, f x ∂μ)| ≤ ⨍ x, |a-f x| ∂μ := by
  have he : (⨍ x, a-f x ∂μ) = a-(⨍ x, f x ∂μ) := by
    have hh := average_sub (integrable_const a : Integrable (fun _ : X => a) μ) hf
    simpa only [Pi.sub_apply, average_const] using hh
  rw [← he]
  exact abs_average_le_average_abs μ _

lemma abs_sub_average_le_of_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hf : Integrable f μ) (a C : ℝ) (h : ∀ᵐ x ∂μ, |a-f x| ≤ C) :
    |a-(⨍ x, f x ∂μ)| ≤ C := by
  apply (abs_sub_average_le_average_abs_sub hf a).trans
  simpa only [Pi.sub_apply, average_const] using
    average_mono_real ((integrable_const a).sub hf).abs (integrable_const C) h

end CircleDomainRigidity

end

end OAI
