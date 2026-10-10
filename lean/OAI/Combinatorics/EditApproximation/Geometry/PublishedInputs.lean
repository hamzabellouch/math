import Mathlib

namespace OAI

/-!
# Finite scalar Bernstein concentration

The only concentration input needed by the coarse estimator and the shared
group sampler is finite scalar Bernstein: Joel A. Tropp, *ACM 217:
Probability in High Dimensions*, Caltech CMS Lecture Notes 2021-01,
corrected March 2023, Theorem 4.16 (printed p. 36).
https://tropp.caltech.edu/notes/Tro21-Probability-High-LN-corr.pdf

`FiniteBernsteinInput` states the bound for centered bounded finite sums
with an upper bound on their summed variances. Independence identifies the
variance of the sum with the sum of the variances. Positivity of the proxy
avoids the zero-denominator case.
-/

namespace EditApproximation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The finite centered-sum specialization of Tropp, Theorem 4.16.
This is the exact Lean proposition to be passed explicitly to downstream
concentration theorems. -/
def FiniteBernsteinInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (bound varianceProxy deviation : ℝ),
    0 < bound → 0 < varianceProxy → 0 < deviation →
    iIndepFun X μ → (∀ i, Measurable (X i)) →
    (∀ i, Integrable (X i) μ) →
    (∀ i, (∫ ω, X i ω ∂μ) = 0) →
    (∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ bound) →
    (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ varianceProxy →
    μ.real {ω | deviation ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-deviation ^ 2 /
        (2 * varianceProxy + (2 / 3 : ℝ) * bound * deviation))

end EditApproximation

end OAI
