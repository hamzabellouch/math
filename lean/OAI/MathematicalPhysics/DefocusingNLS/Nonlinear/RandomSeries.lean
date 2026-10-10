import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-!
# Almost sure finiteness of a random Fourier energy

The Tonelli step used to turn summable expected squared Sobolev coefficients
into almost sure finite Sobolev energy. This lemma does not identify the NLS
flow or assert its existence.
-/

open MeasureTheory
open scoped ENNReal

namespace DefocusingNLS

/-- Summable bounds on the expectations of nonnegative terms imply almost
sure finiteness of their sum. Independence is not needed for this step. -/
theorem ae_tsum_lt_top_of_summable_expectations
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {μ : Measure Ω}
    (F : ι → Ω → ℝ≥0∞) (hF : ∀ i, Measurable (F i))
    (w : ι → ℝ) (hw : Summable w)
    (hbound : ∀ i, ∫⁻ ω, F i ω ∂μ ≤ ENNReal.ofReal (w i)) :
    ∀ᵐ ω ∂μ, (∑' i, F i ω) < ∞ := by
  have hfinite : ∫⁻ ω, (∑' i, F i ω) ∂μ < ∞ := by
    rw [lintegral_tsum (fun i => (hF i).aemeasurable)]
    exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) hw.tsum_ofReal_lt_top
  exact ae_lt_top (Measurable.tsum hF) hfinite.ne

end DefocusingNLS

end OAI
