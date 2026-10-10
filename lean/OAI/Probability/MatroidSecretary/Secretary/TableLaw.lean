import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace OAI

/-!
# Precommitted finite conditional-randomness tables

The secretary construction draws all conditional random choices before the
random arrival permutation.  A table indexed by every possible branch/prefix
pair does this without concealing later randomness.  Its law is the ordinary
finite product measure `Measure.pi κ`.  Evaluating the table after an independent
prefix experiment has exactly the corresponding conditional law.

These lemmas concern only this sampling construction, not the source theorem's
competitive guarantee.  In particular an application must separately prove the
prefix law and the concrete source conditional-kernel laws.
-/

namespace MatroidProphet.Secretary

open MeasureTheory
open scoped BigOperators

variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- All conditional samples can be drawn initially and independently. Evaluating
one coordinate after an independent finite experiment has the prescribed law. -/
theorem integral_precommittedTable
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (index : Ω → ι) (f : ι → α → ℝ) :
    (∫ z : Ω × (ι → α), f (index z.1) (z.2 (index z.1))
      ∂μ.prod (Measure.pi κ)) =
      ∫ ω, ∫ r, f (index ω) r ∂κ (index ω) ∂μ := by
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    exact integral_comp_eval (μ := κ) (i := index ω)
      (f := f (index ω))
      (measurable_of_countable (f (index ω))).aestronglyMeasurable

/-- The same identity with the independent experiment explicitly summed. It
retains the complete table, including all coordinates unused in this run. -/
theorem integral_precommittedTable_eq_sum
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (index : Ω → ι) (f : ι → α → ℝ) :
    (∫ z : Ω × (ι → α), f (index z.1) (z.2 (index z.1))
      ∂μ.prod (Measure.pi κ)) =
      ∑ ω, μ.real {ω} * (∫ r, f (index ω) r ∂κ (index ω)) := by
  rw [integral_precommittedTable]
  simpa only [smul_eq_mul, measureReal_def] using
    (integral_fintype (μ := μ)
      (f := fun ω => ∫ r, f (index ω) r ∂κ (index ω)) Integrable.of_finite)

end MatroidProphet.Secretary

end OAI
