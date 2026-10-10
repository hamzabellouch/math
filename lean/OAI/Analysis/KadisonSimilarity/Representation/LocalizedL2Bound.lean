import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! Localized L² estimates recover pointwise bounds. This is the norm
argument for the columns of an operator commuting with diagonal projections. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma l2_norm_sq_eq_integral (f : Lp H 2 μ) :
    ‖f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  congr 1
  funext a
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f a)).symm

variable [IsFiniteMeasure μ]

omit [CompleteSpace H] in
/-- Bounds on every localized square norm imply an almost-everywhere bound.
The localized vector is allowed to be any representative of the indicator. -/
theorem ae_norm_le_of_localized_square_bound (f : Lp H 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hlocal : ∀ (s : Set Ω), MeasurableSet s →
      ∃ g : Lp H 2 μ, g =ᵐ[μ] s.indicator f ∧ ‖g‖ ^ 2 ≤ C ^ 2 * μ.real s) :
    ∀ᵐ a ∂μ, ‖f a‖ ≤ C := by
  have hf : Integrable (fun a => ‖f a‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hsquares : ∀ᵐ a ∂μ, ‖f a‖ ^ 2 ≤ C ^ 2 := by
    apply ae_le_of_forall_setIntegral_le hf (integrable_const (C ^ 2))
    intro s hs _
    obtain ⟨g, hg, hbound⟩ := hlocal s hs
    have he : ‖g‖ ^ 2 = ∫ a in s, ‖f a‖ ^ 2 ∂μ := by
      rw [l2_norm_sq_eq_integral]
      have heq : (fun a => ‖g a‖ ^ 2) =ᵐ[μ] s.indicator (fun a => ‖f a‖ ^ 2) := by
        filter_upwards [hg] with a ha
        rw [ha]
        by_cases h : a ∈ s <;> simp [h]
      rw [integral_congr_ae heq, integral_indicator hs]
    rw [← he]
    simpa [measureReal_def, mul_comm] using hbound
  filter_upwards [hsquares] with a ha
  exact (sq_le_sq₀ (norm_nonneg _) hC).mp ha

end KadisonSimilarity

end

end OAI
