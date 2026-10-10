import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.BalancedRyser.Probability.WithoutReplacementCoupling

namespace OAI

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Balanced.WithoutReplacement

theorem uniformOfFinset_product_apply {α β : Type*}
    (s : Finset α) (t : Finset β) (hs : s.Nonempty) (ht : t.Nonempty)
    (x : α) (y : β) :
    PMF.uniformOfFinset (s ×ˢ t) (hs.product ht) (x, y) =
      PMF.uniformOfFinset s hs x * PMF.uniformOfFinset t ht y := by
  classical
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ t <;>
    simp [PMF.uniformOfFinset_apply, hx, hy, Finset.card_product,
      ENNReal.mul_inv]

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∫ x, f x ∂(PMF.uniformOfFinset s hs).toMeasure = 𝔼 x ∈ s, f x := by
  classical
  rw [PMF.integral_eq_sum, Finset.expect_eq_sum_div_card]
  simp [PMF.uniformOfFinset_apply, apply_ite, ite_mul,
    div_eq_inv_mul, ← Finset.mul_sum]

theorem variance_uniformOfFinset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    variance f (PMF.uniformOfFinset s hs).toMeasure = finiteVariance s f := by
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable,
    integral_uniformOfFinset, integral_uniformOfFinset]
  rfl

end Balanced.WithoutReplacement

end OAI
