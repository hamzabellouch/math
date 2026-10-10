import Mathlib.Analysis.Real.Sqrt
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

namespace PerfectCompleteness.DensityVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_sub (μ : FiniteDistribution Ω) (f g : Ω → ℝ) :
    μ.expectation (fun x => f x - g x) = μ.expectation f - μ.expectation g := by
  simp only [FiniteDistribution.expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (μ : FiniteDistribution Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x * c) = μ.expectation f * c := by
  simp only [FiniteDistribution.expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_div (μ : FiniteDistribution Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x / c) = μ.expectation f / c := by
  simpa only [div_eq_mul_inv] using expectation_mul_const μ f c⁻¹

def reweight (μ : FiniteDistribution Ω) (density : Ω → ℝ)
    (nonnegative : ∀ x, 0 ≤ density x) (mean_one : μ.expectation density = 1) :
    FiniteDistribution Ω where
  weight x := μ.weight x * density x
  nonnegative x := mul_nonneg (μ.nonnegative x) (nonnegative x)
  normalized := mean_one

theorem variation_eq_density (μ ν : FiniteDistribution Ω) (density : Ω → ℝ)
    (h : ∀ x, ν.weight x = μ.weight x * density x) :
    ν.totalVariation μ = μ.expectation (fun x => |density x - 1|) / 2 := by
  unfold FiniteDistribution.totalVariation FiniteDistribution.expectation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [h x, show μ.weight x * density x - μ.weight x =
    μ.weight x * (density x - 1) by ring, abs_mul,
    abs_of_nonneg (μ.nonnegative x)]

theorem variation_le_sqrt (μ ν : FiniteDistribution Ω) (density : Ω → ℝ)
    (h : ∀ x, ν.weight x = μ.weight x * density x) (v : ℝ)
    (hv : μ.expectation (fun x => (density x - 1) ^ 2) ≤ v) :
    ν.totalVariation μ ≤ Real.sqrt v / 2 := by
  rw [variation_eq_density μ ν density h]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.le_sqrt_of_sq_le
  have hcs := UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le μ.weight
    (fun x => |density x - 1|) ⟨μ.nonnegative, μ.normalized⟩
  change μ.expectation (fun x => |density x - 1|) ^ 2 ≤
    μ.expectation (fun x => |density x - 1| ^ 2) at hcs
  simpa only [sq_abs] using hcs.trans (by simpa only [sq_abs] using hv)

theorem variation_pushforward_le (μ ν : FiniteDistribution Ω) (observe : Ω → Γ) :
    (μ.pushforward observe).totalVariation (ν.pushforward observe) ≤
      μ.totalVariation ν := by
  classical
  unfold FiniteDistribution.totalVariation
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  have hdiff (y : Γ) :
      (μ.pushforward observe).weight y - (ν.pushforward observe).weight y =
        ∑ x, if observe x = y then μ.weight x - ν.weight x else 0 := by
    simp only [FiniteDistribution.pushforward, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : observe x = y <;> simp [hx]
  calc
    _ ≤ ∑ y, ∑ x, if observe x = y then |μ.weight x - ν.weight x| else 0 := by
      apply Finset.sum_le_sum
      intro y _
      rw [hdiff]
      calc
        _ ≤ ∑ x, |if observe x = y then μ.weight x - ν.weight x else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = _ := by rw [Finset.sum_comm]; simp

theorem observed_variation_le_sqrt (μ ν : FiniteDistribution Ω) (density : Ω → ℝ)
    (h : ∀ x, ν.weight x = μ.weight x * density x) (v : ℝ)
    (hv : μ.expectation (fun x => (density x - 1) ^ 2) ≤ v)
    (observe : Ω → Γ) :
    (ν.pushforward observe).totalVariation (μ.pushforward observe) ≤ Real.sqrt v / 2 :=
  (variation_pushforward_le ν μ observe).trans (variation_le_sqrt μ ν density h v hv)

end
end PerfectCompleteness.DensityVariation

end

end OAI
