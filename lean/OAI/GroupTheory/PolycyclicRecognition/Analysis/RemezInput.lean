import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Scalar polynomial sublevel estimates

M. I. Ganzburg, *A multivariate Remez-type inequality with φ-concave
weights*, Colloquium Mathematicum 147 (2017), 221–240, Theorem 1.2(a),
p. 222, DOI 10.4064/cm6884-7-2016.

The sharp estimate gives a coarse cube specialization. Its Chebyshev factor
is bounded by `(4 n |V| / |S|)^D`, using
`1 - (1 - t)^(1/n) ≥ t/n` and `T_D(x) ≤ (2*x)^D` for `x ≥ 1`.
For the cube `V = [-R,R]^n`, its volume is at most `2^n (1+R)^n`.
A fixed constant absorbs these factors. Coordinate slicing also proves
the weaker exponent `n * D`, which suffices for the image-volume estimates.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory

/-- The precise published input used to keep mass away from a polynomial's
zero set. The constant depends only on the dimension and degree. -/
def RemezPolynomialInput : Prop :=
  ∀ n D : ℕ, 1 ≤ n → 1 ≤ D → ∃ A : ℝ, 0 < A ∧
    ∀ (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ D →
    ∀ R : ℝ, 1 ≤ R → ∀ S : Set (Fin n → ℝ),
    MeasurableSet S → S ⊆ closedBall 0 R → 0 < (volume S).toReal →
    ∀ η : ℝ, 0 ≤ η → (∀ x ∈ S, |MvPolynomial.eval x p| ≤ η) →
    ∀ x ∈ closedBall 0 R,
      |MvPolynomial.eval x p| ≤
        (A * (1 + R) ^ n / (volume S).toReal) ^ (n * D) * η

end PolycyclicRecognition

end

end OAI
