import OAI.Analysis.MarkovType.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem weighted_tail_power_le {Ω : Type*} [Fintype Ω]
    (w F : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hF : ∀ ω, 0 ≤ F ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    c ^ p * (∑ ω, if c ≤ F ω then w ω else 0) ≤
      ∑ ω, w ω * (F ω) ^ p := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : c ≤ F ω
  · simp only [ite_eq_left h]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc h hp) (hw ω)
  · simp only [ite_eq_right h, mul_zero]
    exact mul_nonneg (hw ω) (Real.rpow_nonneg (hF ω) p)

theorem FiniteLaw.tail_power_mul_prob_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) :
    c ^ p * μ.prob (fun ω => c ≤ F ω) ≤ μ.expect (fun ω => (F ω) ^ p) := by
  classical
  exact weighted_tail_power_le μ.mass F μ.mass_nonneg hF hc hp

theorem FiniteLaw.tail_mass_power_le_expect {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (F : Ω → ℝ) (hF : ∀ ω, 0 ≤ F ω)
    {c p a : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (ha : a ≤ μ.prob (fun ω => c ≤ F ω)) :
    a * c ^ p ≤ μ.expect (fun ω => (F ω) ^ p) := by
  calc
    a * c ^ p ≤ μ.prob (fun ω => c ≤ F ω) * c ^ p :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hc p)
    _ = c ^ p * μ.prob (fun ω => c ≤ F ω) := mul_comm _ _
    _ ≤ μ.expect (fun ω => (F ω) ^ p) := μ.tail_power_mul_prob_le F hF hc hp

end MarkovSuperreflexivity

end

end OAI
