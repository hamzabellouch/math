import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Basic

namespace OAI

/-!
# Published short-interval inputs for the joint Dickman problem

These definitions are *propositions to be supplied as hypotheses*. They are not
axioms or proofs of the cited analytic theorems. In particular they do not
assume joint independence at the shift one, the manuscript's new mixed
decorrelation proposition, or any of its graph estimates.

The natural-number floor is harmless here: all intervals to which the inputs
apply have positive left endpoint. `Finset.Ioc` implements the convention
`z < n ≤ z + H`; changing the inclusion of the endpoints has the elementary
`O(1 / H)` cost recorded in the manuscript.
-/

namespace JointDickman.PublishedInputs

open Filter MeasureTheory
open scoped Topology

/-- A real short average, with the manuscript's open-left endpoint convention. -/
noncomputable def realShortAverage (f : ArithmeticFunction ℝ) (H z : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊, f n) / H

/-- A complex short average with the same endpoint convention. -/
noncomputable def complexShortAverage (f : ArithmeticFunction ℂ) (H z : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊z + H⌋₊, f n) / (H : ℂ)

/-- The mean on the dyadic interval `(X, 2X]`. -/
noncomputable def realLongAverage (f : ArithmeticFunction ℝ) (X : ℝ) : ℝ :=
  realShortAverage f X X

/-- The mean-square comparison needed from Matomäki and Radziwiłł,
*Multiplicative functions in short intervals*, Ann. of Math. 183 (2016),
Theorem 1, DOI `10.4007/annals.2016.183.3.6`, arXiv:1501.04585v4.

Theorem 1 is uniform in the multiplicative function, interval length, and
exceptional-set tolerance. Its uniform exceptional-set bound and boundedness
give this mean-square consequence (manuscript Theorem `labels-real-MR`). -/
def RealShortIntervalInput : Prop :=
  ∃ r : ℝ → ℝ,
    Tendsto r atTop (𝓝 0) ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative →
      (∀ n : ℕ, |f n| ≤ 1) →
      ∀ H X : ℝ, 2 ≤ H → H ≤ X →
        (1 / X) * (∫ z in X..2 * X,
          |realShortAverage f H z - realLongAverage f X| ^ 2) ≤ r H

/-- The squared pretentious distance from `n ↦ n^(it)` up to `X`. -/
noncomputable def primeDistanceSquared (f : ArithmeticFunction ℂ) (X t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * Complex.exp (-((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)).re) /
      (p : ℝ)

/-- The minimum squared distance over the frequency interval `[-X, X]`. -/
noncomputable def minimumDistance (f : ArithmeticFunction ℂ) (X : ℝ) : ℝ :=
  sInf ((fun t : ℝ => primeDistanceSquared f X t) '' Set.Icc (-X) X)

/-- The quantitative complex short-average input from Matomäki, Radziwiłł,
and Tao, *An averaged form of Chowla's conjecture*, Algebra & Number Theory 9
(2015), Theorem A.1, DOI `10.2140/ant.2015.9.2167`.

The source is the corrected arXiv:1503.05121v3 (1 March 2022); the correction
after Proposition A.3 permits `exp (-M)`. The weaker `(1 + M) * exp (-M)`
used here is the manuscript's Theorem `labels-complex-MRT` and also covers
small `M`. The absolute implied constant is represented by `C`. -/
def ComplexShortIntervalInput : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℂ), f.IsMultiplicative →
      (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ H X : ℝ, 10 ≤ H → H ≤ X →
        (1 / X) * (∫ z in X..2 * X, ‖complexShortAverage f H z‖ ^ 2) ≤
          C * ((1 + minimumDistance f X) * Real.exp (-minimumDistance f X) +
            (Real.log (Real.log H) / Real.log H) ^ 2 +
            (Real.log X) ^ (-(1 : ℝ) / 50))

end JointDickman.PublishedInputs

end OAI
