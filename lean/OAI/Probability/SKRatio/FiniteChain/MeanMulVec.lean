import Mathlib
import OAI.Probability.SKRatio.FiniteChain.VarianceNonneg

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem mean_mulVec (p : α → ℝ) (A : Matrix α α ℝ) (f : α → ℝ) :
    mean p (A *ᵥ f) = mean (p ᵥ* A) f := by
  simp only [mean, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteLaw

theorem discreteDistance_smoothing {n : ℕ} (g : Disorder n) (k s : ℕ)
    {ε V W : ℝ} (hε : 0 < ε) (hoverlap : discreteDistance g k ≤ 1 - ε)
    (htransient : ∀ (x : Spin n) (f : Spin n → ℝ), (∀ y, |f y| ≤ 1) →
      FiniteLaw.variance ((transition g ^ k) x) ((transition g ^ s) *ᵥ f) ≤ V)
    (hequilibrium : ∀ f : Spin n → ℝ, (∀ y, |f y| ≤ 1) →
      FiniteLaw.variance (mass g 0) ((transition g ^ s) *ᵥ f) ≤ W) :
    discreteDistance g (k + s) ≤ (Real.sqrt V + Real.sqrt W) / (2 * Real.sqrt ε) := by
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  have hP := transition_pow_stochastic g k
  have hc := FiniteLaw.common_mass_means ((transition g ^ k) x) (mass g 0)
    ((transition g ^ s) *ᵥ f) (hP.1 x) (mass_nonneg g 0)
    (Matrix.sum_row_of_mem_rowStochastic hP x) (sum_mass g 0) hε
    ((tv_le_discreteDistance g k x).trans hoverlap)
  rw [FiniteLaw.mean_mulVec, FiniteLaw.mean_mulVec, transition_pow_stationary] at hc
  rw [pow_add, Matrix.mul_apply_eq_vecMul]
  calc
    _ ≤ (Real.sqrt (FiniteLaw.variance ((transition g ^ k) x) ((transition g ^ s) *ᵥ f)) +
        Real.sqrt (FiniteLaw.variance (mass g 0) ((transition g ^ s) *ᵥ f))) / Real.sqrt ε := hc
    _ ≤ (Real.sqrt V + Real.sqrt W) / Real.sqrt ε := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact add_le_add (Real.sqrt_le_sqrt (htransient x f hf))
        (Real.sqrt_le_sqrt (hequilibrium f hf))
    _ = _ := by ring

end SKRatio

end
end
end
end
end

end OAI
