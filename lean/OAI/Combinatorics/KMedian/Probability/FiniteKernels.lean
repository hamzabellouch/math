import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLawConstructions

namespace OAI

namespace MetricKMedian.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  weight ξ := ∑ ω, μ.weight ω*(κ ω).weight ξ
  nonneg ξ := Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) ((κ ω).nonneg ξ))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

theorem expect_bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ξ → ℝ) :
    (μ.bind κ).expect f = μ.expect (fun ω => (κ ω).expect f) := by
  simp only [bind, expect, Finset.sum_mul, mul_assoc, Finset.mul_sum]
  exact Finset.sum_comm

theorem property_bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (R : Ξ → Prop)
    (hR : ∀ ω, 0 < μ.weight ω → ∀ ξ, 0 < (κ ω).weight ξ → R ξ) :
    ∀ ξ, 0 < (μ.bind κ).weight ξ → R ξ := by
  intro ξ hξ
  by_contra hn
  have hpoint : ∀ ω, μ.weight ω*(κ ω).weight ξ=0 := by
    intro ω
    by_cases hω : 0 < μ.weight ω
    · have hk : (κ ω).weight ξ=0 := by
        apply le_antisymm _ ((κ ω).nonneg ξ)
        by_contra hneg
        exact hn (hR ω hω ξ (lt_of_not_ge hneg))
      rw [hk, mul_zero]
    · rw [le_antisymm (le_of_not_gt hω) (μ.nonneg ω), zero_mul]
  have hz : (μ.bind κ).weight ξ=0 := Finset.sum_eq_zero (fun ω _ => hpoint ω)
  rw [hz] at hξ
  exact lt_irrefl _ hξ

noncomputable def map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ :=
  μ.bind (fun ω => dirac (f ω))

theorem expect_map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (μ.map f).expect g=μ.expect (fun ω => g (f ω)) := by
  rw [map, expect_bind]
  simp_rw [expect_dirac]

theorem property_map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (R : Ξ → Prop)
    (hR : ∀ ω, 0 < μ.weight ω → R (f ω)) :
    ∀ ξ, 0 < (μ.map f).weight ξ → R ξ := by
  apply property_bind
  intro ω hω ξ hξ
  by_cases heq : ξ=f ω
  · rw [heq]; exact hR ω hω
  · simp only [dirac, ite_eq_right heq] at hξ
    exact False.elim (lt_irrefl _ hξ)

omit [Fintype Ξ] in
theorem property_mix (μ ν : FiniteLaw Ω) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (R : Ω → Prop) (hμ : ∀ ω, 0 < μ.weight ω → R ω)
    (hν : ∀ ω, 0 < ν.weight ω → R ω) :
    ∀ ω, 0 < (mix θ hθ0 hθ1 μ ν).weight ω → R ω := by
  intro ω hω
  by_cases hp : 0 < μ.weight ω
  · exact hμ ω hp
  · have hz : μ.weight ω=0 := le_antisymm (le_of_not_gt hp) (μ.nonneg ω)
    by_cases hq : 0 < ν.weight ω
    · exact hν ω hq
    · have hzν : ν.weight ω=0 := le_antisymm (le_of_not_gt hq) (ν.nonneg ω)
      simp only [mix, hz, hzν, mul_zero, add_zero] at hω
      exact False.elim (lt_irrefl _ hω)

end MetricKMedian.FiniteLaw

end OAI
