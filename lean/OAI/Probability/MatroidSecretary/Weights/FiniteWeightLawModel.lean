import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace OAI

namespace MatroidProphet.FiniteLaw

open MeasureTheory
open scoped BigOperators

noncomputable def weightPMF {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a), hp1]
    exact ENNReal.ofReal_one)

noncomputable def weightMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) : Measure α :=
  (weightPMF p hp hp1).toMeasure

noncomputable def kernelJointPMF {α β : Type*} [Fintype α] [Fintype β]
    (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1) : PMF (β × α) :=
  weightPMF (fun ba => m ba.1 * k ba.1 ba.2)
    (fun ba => mul_nonneg (hm ba.1) (hk ba.1 ba.2)) (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, hk1, mul_one]
      exact hm1)

noncomputable def kernelJointMeasure {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1) : Measure (β × α) :=
  (kernelJointPMF m k hm hm1 hk hk1).toMeasure

end MatroidProphet.FiniteLaw

end OAI
