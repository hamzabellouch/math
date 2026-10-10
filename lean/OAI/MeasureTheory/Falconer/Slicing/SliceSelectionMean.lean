import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace OAI

/-! # Selecting a retained slice from its quantitative mean -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem exists_large_slice_of_mean (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℝ≥0∞) (hsupport : ∀ᵐ x ∂μ, x ∉ S → f x = 0) {a : ℝ≥0∞}
    (hmean : a*μ S < ∫⁻ x, f x ∂μ) :
    ∃ x ∈ S, a < f x := by
  by_contra! hn
  have hle : f ≤ᵐ[μ] S.indicator (fun _ => a) := by
    filter_upwards [hsupport] with x hx
    by_cases hxs : x ∈ S
    · simpa only [indicator_of_mem hxs] using hn x hxs
    · simp only [hx hxs,indicator_of_notMem hxs,le_refl]
  have hi := lintegral_mono_ae hle
  rw [lintegral_indicator_const hS] at hi
  exact (not_le_of_gt hmean) hi

end Falconer

end OAI
