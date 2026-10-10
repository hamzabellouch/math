import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X R Z : Type*} [Fintype X] [MeasurableSpace Z]
  (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (μ : Measure Z)
  (D : X → Z → ℝ)

theorem fiberMean_integrable (hD : ∀ x, Integrable (D x) μ) :
    Integrable (fun z => p.fiberMean F r (fun x => D x z)) μ := by
  classical
  unfold fiberMean mean
  apply integrable_finsetSum
  intro x _
  by_cases hx : F x = r
  · simpa only [hx, ite_true] using (hD x).const_mul (p.weight x)
  · simp only [hx, ite_false, mul_zero]
    exact integrable_zero _ _ _

theorem integral_fiberMean (hD : ∀ x, Integrable (D x) μ) :
    (∫ z, p.fiberMean F r (fun x => D x z) ∂μ) =
      p.fiberMean F r (fun x => ∫ z, D x z ∂μ) := by
  classical
  unfold fiberMean mean
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : F x = r
    · simp only [hx, ite_true, integral_const_mul]
    · simp only [hx, ite_false, mul_zero, integral_zero]
  · intro x _
    by_cases hx : F x = r
    · simpa only [hx, ite_true] using (hD x).const_mul (p.weight x)
    · simp only [hx, ite_false, mul_zero]
      exact integrable_zero _ _ _

theorem fiberMean_density_mass [Fintype R] (hD : ∀ x, Integrable (D x) μ)
    (hm : ∀ x, (∫ z, D x z ∂μ) = 1) :
    (∫ z, p.fiberMean F r (fun x => D x z) ∂μ) = (p.fiberLaw F).weight r := by
  rw [p.integral_fiberMean F r μ D hD, fiberLaw_weight]
  simp only [hm]

theorem fiberMean_density_total_mass [Fintype R] (hD : ∀ x, Integrable (D x) μ)
    (hm : ∀ x, (∫ z, D x z ∂μ) = 1) :
    (∑ r, ∫ z, p.fiberMean F r (fun x => D x z) ∂μ) = 1 := by
  simp_rw [p.fiberMean_density_mass F _ μ D hD hm]
  exact (p.fiberLaw F).total

theorem fiberMean_normalized_density [Fintype R] (hD : ∀ x, Integrable (D x) μ)
    (hm : ∀ x, (∫ z, D x z ∂μ) = 1) (hD0 : ∀ x z, 0 ≤ D x z)
    (hr : 0 < (p.fiberLaw F).weight r) :
    (∀ z, 0 ≤ p.fiberMean F r (fun x => D x z) / (p.fiberLaw F).weight r) ∧
    Integrable (fun z => p.fiberMean F r (fun x => D x z) / (p.fiberLaw F).weight r) μ ∧
    (∫ z, p.fiberMean F r (fun x => D x z) / (p.fiberLaw F).weight r ∂μ) = 1 := by
  refine ⟨fun z => div_nonneg (p.fiberMean_nonneg F r _ (fun x => hD0 x z)) hr.le,
    (p.fiberMean_integrable F r μ D hD).div_const _, ?_⟩
  rw [integral_div, p.fiberMean_density_mass F r μ D hD hm, div_self hr.ne']

end Erdos3.FiniteProbabilityWeights

end

end OAI
