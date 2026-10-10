import OAI.Analysis.KadisonKastler.FrequencyNest
import OAI.Analysis.KadisonKastler.NestAveraging

namespace OAI

/-! # Frequency-cut ranges as almost-everywhere support conditions -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Being fixed by the actual frequency projection is exactly the usual
almost-everywhere support condition on the `L²` Fourier transform. -/
theorem regularFrequencyProjection_fixed_iff (a : ℝ) (f : RegularCoreHilbert H) :
    regularFrequencyProjection a f = f ↔
      ∀ᵐ t : ℝ, t ≤ a / (2 * Real.pi) → (𝓕 f : RegularCoreHilbert H) t = 0 := by
  constructor
  · intro h
    have hp := regularFrequencyProjection_apply_fourier a f
    rw [h] at hp
    filter_upwards [hp] with t ht hle
    rw [ht, Set.indicator_of_notMem (show t ∉ Set.Ioi (a / (2 * Real.pi)) from not_lt.mpr hle)]
  · intro h
    apply (Lp.fourierTransformₗᵢ ℝ H).injective
    apply Lp.ext
    filter_upwards [regularFrequencyProjection_apply_fourier a f, h] with t hp ht
    change (𝓕 (regularFrequencyProjection a f) : RegularCoreHilbert H) t =
      (𝓕 f : RegularCoreHilbert H) t
    rw [hp]
    by_cases hmem : t ∈ Set.Ioi (a / (2 * Real.pi))
    · exact Set.indicator_of_mem hmem _
    · rw [Set.indicator_of_notMem hmem]
      exact (ht (le_of_not_gt hmem)).symm

/-- A nest-preserving operator preserves every positive-frequency
subspace with the corresponding shifted threshold. -/
theorem frequency_support_of_preserves_nest
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : PreservesProjectionNest regularFrequencyNest T)
    (a : ℝ) (f : RegularCoreHilbert H)
    (hf : ∀ᵐ t : ℝ, t ≤ a / (2 * Real.pi) → (𝓕 f : RegularCoreHilbert H) t = 0) :
    ∀ᵐ t : ℝ, t ≤ a / (2 * Real.pi) → (𝓕 (T f) : RegularCoreHilbert H) t = 0 := by
  apply (regularFrequencyProjection_fixed_iff a (T f)).mp
  have hp := (regularFrequencyProjection_fixed_iff a f).mpr hf
  have hz := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f)
    (hT (-a))
  change (1 - regularFrequencyProjection (- -a))
    (T (regularFrequencyProjection (- -a) f)) = 0 at hz
  rw [neg_neg, hp, sub_apply, one_apply_eq_self, sub_eq_zero] at hz
  exact hz.symm

end

end KadisonKastler

end OAI
