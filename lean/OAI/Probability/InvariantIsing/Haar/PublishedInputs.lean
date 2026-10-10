import Mathlib

namespace OAI

/-!
Haar concentration and Gaussian Poincaré inequalities.

Gromov–Milman, *A topological application of the isoperimetric inequality*,
American Journal of Mathematics 105 (1983), 843–854, Section 1.2,
Remark 2, and the special-orthogonal example in Section 3.4 give the
following concentration specialization.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal

namespace InvariantIsing

abbrev SpecialOrthogonal (N : ℕ) := Matrix.specialOrthogonalGroup (Fin N) ℝ

/-- Frobenius distance, with the unnormalized matrix-coordinate convention. -/
def frobeniusDistance {N : ℕ} (U V : SpecialOrthogonal N) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j -
    (V : Matrix (Fin N) (Fin N) ℝ) i j) ^ 2)

/-- Haar concentration for arbitrary
Frobenius-Lipschitz observables on `SO(N)`. The constants are uniform in
dimension, observable, and Lipschitz constant. -/
def HaarConcentrationInput : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ f : SpecialOrthogonal N → ℝ, Measurable f →
    ∀ L : ℝ, 0 < L →
      (∀ U V, |f U - f V| ≤ L * frobeniusDistance U V) →
    ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ μ.real {U | f U ≤ m} ∧
      (1 / 2 : ℝ) ≤ μ.real {U | m ≤ f U} ∧
      ∀ r : ℝ, 0 < r →
        μ.real {U | r ≤ |f U - m|} ≤
          C * Real.exp (-c * (N : ℝ) * r ^ 2 / L ^ 2)

/-- The finite-dimensional Gaussian Poincaré inequality specialized to a
globally Lipschitz function. The Euclidean norm is essential: a coordinatewise
bound for the supremum norm would introduce a dimension factor.

Published source: Bakry–Émery, *Diffusions hypercontractives*, Séminaire de
Probabilités XIX (1985), Proposition 5, equation (20), p.198, with `U(x)=x²`,
and Corollary 2, equation (23), p.199, with the Ornstein–Uhlenbeck example
on pp.199–200 (the carré-du-champ calculation is on p.186). The usual
Lipschitz specialization follows by smooth approximation. -/
def GaussianLipschitzVarianceInput : Prop :=
  ∀ d : ℕ, ∀ L : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
    LipschitzWith L f →
      ProbabilityTheory.variance f (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
        (L : ℝ) ^ 2

end InvariantIsing

end

end OAI
