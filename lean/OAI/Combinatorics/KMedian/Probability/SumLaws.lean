import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) : FiniteLaw (Ω ⊕ Ξ) where
  weight := Sum.elim (fun ω => θ*μ.weight ω) (fun ξ => (1-θ)*ν.weight ξ)
  nonneg := by
    intro z
    cases z with
    | inl ω => exact mul_nonneg hθ0 (μ.nonneg ω)
    | inr ξ => exact mul_nonneg (sub_nonneg.mpr hθ1) (ν.nonneg ξ)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum, μ.total, ν.total]
    ring

theorem expect_sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω ⊕ Ξ → ℝ) :
    (sumMix θ hθ0 hθ1 μ ν).expect f =
      θ*μ.expect (fun ω => f (.inl ω))+(1-θ)*ν.expect (fun ξ => f (.inr ξ)) := by
  simp only [expect, sumMix, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    mul_assoc, Finset.mul_sum]

theorem property_sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (R : Ω ⊕ Ξ → Prop)
    (hμ : ∀ ω, 0 < μ.weight ω → R (.inl ω))
    (hν : ∀ ξ, 0 < ν.weight ξ → R (.inr ξ)) :
    ∀ z, 0 < (sumMix θ hθ0 hθ1 μ ν).weight z → R z := by
  intro z hz
  cases z with
  | inl ω =>
    apply hμ ω
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) (μ.nonneg ω)
    simp only [sumMix, Sum.elim_inl, heq, mul_zero] at hz
    exact lt_irrefl _ hz
  | inr ξ =>
    apply hν ξ
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) (ν.nonneg ξ)
    simp only [sumMix, Sum.elim_inr, heq, mul_zero] at hz
    exact lt_irrefl _ hz

end MetricKMedian.FiniteLaw

end OAI
