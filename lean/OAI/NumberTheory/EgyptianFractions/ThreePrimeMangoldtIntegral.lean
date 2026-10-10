import OAI.NumberTheory.EgyptianFractions.ThreePrimeContinuousFourier
import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldt

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeContinuousFourier

/-- The actual positive-frequency Mangoldt polynomial on the unit circle. -/
def mangoldtPhaseSum (u : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 u, (ArithmeticFunction.vonMangoldt n : ℂ) * phase (n : ℤ) x

lemma mangoldtPhaseSum_exp (u : ℕ) (x : ℝ) :
    mangoldtPhaseSum u x = ∑ n ∈ Finset.Icc 1 u,
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * x) := by
  simp only [mangoldtPhaseSum, phase_exp, Int.cast_natCast]

lemma mangoldtPhaseSum_continuous (u : ℕ) : Continuous (mangoldtPhaseSum u) := by
  unfold mangoldtPhaseSum
  exact continuous_finsetSum _ (fun n hn => continuous_const.mul (phase_continuous _))

/-- Exact continuous cubic extraction for the canonical positive-integer
Mangoldt convolution. In particular no prime-distribution estimate is used. -/
theorem mangoldt_triple_integral (u : ℕ) :
    (∫ x in (0 : ℝ)..1, mangoldtPhaseSum u x ^ 3 * phase (-(u : ℤ)) x) =
      (mangoldtTripleSum u : ℂ) := by
  classical
  have h := weighted_triple_finset_integral (Finset.Icc 1 u)
    (fun n : ℕ => (n : ℤ)) (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (u : ℤ)
  change (∫ x in (0 : ℝ)..1,
      (∑ n ∈ Finset.Icc 1 u, (ArithmeticFunction.vonMangoldt n : ℂ) *
        phase (n : ℤ) x) ^ 3 * phase (-(u : ℤ)) x) = _
  rw [h]
  unfold mangoldtTripleSum supplyIntegerTriples
  simp only [Finset.sum_filter, Finset.sum_product, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have heq : ((a : ℤ) + (b : ℤ) + (c : ℤ) = (u : ℤ)) ↔ a + b + c = u := by omega
  by_cases hsum : a + b + c = u <;> simp [heq, hsum]

/-- The integral is a genuine integrable complex expression, not an appeal to
the default value of the Bochner integral on a nonintegrable function. -/
theorem mangoldt_cubic_intervalIntegrable (u : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun x => mangoldtPhaseSum u x ^ 3 * phase (-(u : ℤ)) x) MeasureTheory.volume a b := by
  exact ((mangoldtPhaseSum_continuous u).pow 3 |>.mul
    (phase_continuous _)).intervalIntegrable _ _

/-- Taking real parts recovers exactly the real arithmetic convolution. -/
theorem re_mangoldt_triple_integral (u : ℕ) :
    (∫ x in (0 : ℝ)..1, mangoldtPhaseSum u x ^ 3 * phase (-(u : ℤ)) x).re =
      mangoldtTripleSum u := by
  rw [mangoldt_triple_integral]
  rfl

end Problem337.ThreePrimeContinuousFourier

end

end OAI
