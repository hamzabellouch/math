import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Group.Equiv.Basic
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI

section

namespace PerfectCompleteness.UniformDifference

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B H : Type*} [Fintype B] [Fintype H] [AddGroup H]

def difference (old : B → H) (p : B × H) : B × H := (p.1, p.2 - old p.1)

theorem expectation_difference (μ : FiniteDistribution B) (old : B → H)
    (f : B × H → ℝ) :
    (μ.product (FiniteDistribution.uniform H)).expectation
        (fun p => f (difference old p)) =
      (μ.product (FiniteDistribution.uniform H)).expectation f := by
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro b
  rw [FiniteDistribution.expectation_uniform, FiniteDistribution.expectation_uniform]
  simpa only [Fintype.expect_eq_sum_div_card, difference, sub_eq_add_neg] using
    Fintype.expect_equiv (Equiv.addRight (-old b))
      (fun h : H => f (b, h - old b)) (fun h : H => f (b, h))
      (fun _ => by simp only [sub_eq_add_neg]; rfl)

theorem difference_law (μ : FiniteDistribution B) (old : B → H) :
    (μ.product (FiniteDistribution.uniform H)).pushforward (difference old) =
      μ.product (FiniteDistribution.uniform H) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  have h := expectation_difference μ old (fun p => if p = z then (1 : ℝ) else 0)
  rw [← FiniteDistribution.expectation_pushforward
    (μ.product (FiniteDistribution.uniform H)) (difference old)
    (fun p => if p = z then (1 : ℝ) else 0)] at h
  simpa only [FiniteDistribution.expectation, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem observed_difference_law {P : Type*} [Fintype P]
    (μ : FiniteDistribution B) (old : B → H) (observe : B → P) :
    (μ.product (FiniteDistribution.uniform H)).pushforward
        (fun p => (observe p.1, p.2 - old p.1)) =
      (μ.product (FiniteDistribution.uniform H)).pushforward
        (fun p => (observe p.1, p.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution (B × H) => ν.pushforward (fun p => (observe p.1, p.2)))
    (difference_law μ old)
  rw [FiniteDistribution.pushforward_comp] at h
  exact h

end
end PerfectCompleteness.UniformDifference

end

end OAI
