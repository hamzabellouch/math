import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Sampling
import OAI.Combinatorics.IndependentSets.Repetition.Conditionals

namespace OAI

namespace IndependentSetsGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

theorem totalVariation_nonnegative (μ ν : FiniteDistribution Ω) :
    0 ≤ μ.totalVariation ν :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem totalVariation_comm (μ ν : FiniteDistribution Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_abs_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    |μ.probability event - ν.probability event| ≤ μ.totalVariation ν := by
  apply abs_le.mpr
  constructor
  · have h := ν.probability_sub_le_totalVariation μ event
    rw [totalVariation_comm] at h
    linarith
  · exact μ.probability_sub_le_totalVariation ν event

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end IndependentSetsGames.Foundations.Games.FiniteDistribution

namespace IndependentSetsGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem gameLaw_isProbability (μ : Games.FiniteDistribution α) : IsProbability μ.weight :=
  ⟨μ.nonnegative, μ.normalized⟩

def toGameLaw (p : α → ℝ) (hp : IsProbability p) : Games.FiniteDistribution α where
  weight := p
  nonnegative := hp.1
  normalized := hp.2

def gameLawEquiv : Games.FiniteDistribution α ≃ {p : α → ℝ // IsProbability p} where
  toFun μ := ⟨μ.weight, gameLaw_isProbability μ⟩
  invFun p := toGameLaw p.1 p.2
  left_inv μ := by cases μ; rfl
  right_inv p := by cases p; rfl

theorem totalVariation_gameLaw (μ ν : Games.FiniteDistribution α) :
    totalVariation μ.weight ν.weight = μ.totalVariation ν := rfl

noncomputable def gameConditionalKernel (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) : Games.FiniteDistribution β :=
  toGameLaw (conditionalKernel μ.weight fallback.weight a)
    (conditionalKernel_isProbability μ.weight fallback.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) a)

theorem gameConditionalKernel_recombine (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) (b : β) :
    firstMarginal μ.weight a * (gameConditionalKernel μ fallback a).weight b =
      μ.weight (a, b) :=
  marginal_mul_conditionalKernel μ.weight fallback.weight (gameLaw_isProbability μ) a b

noncomputable def gameConditionalProduct (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (newInput : Games.FiniteDistribution α) :
    Games.FiniteDistribution (α × β) :=
  toGameLaw (fun ab => newInput.weight ab.1 * conditionalKernel μ.weight fallback.weight ab.1 ab.2)
    (alternativeInput_conditionalProduct_isProbability μ.weight fallback.weight newInput.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) (gameLaw_isProbability newInput))

theorem gameConditionalProduct_weight (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (newInput : Games.FiniteDistribution α)
    (a : α) (b : β) :
    (gameConditionalProduct μ fallback newInput).weight (a, b) =
      newInput.weight a * (gameConditionalKernel μ fallback a).weight b := rfl

theorem gameCondition_weight (μ : Games.FiniteDistribution α) (event : α → Bool)
    (positive : 0 < μ.probability event) :
    (μ.condition event positive).weight =
      posterior μ.weight (fun a => if event a then 1 else 0) (μ.probability event) := by
  funext a
  cases he : event a <;> simp [Games.FiniteDistribution.condition, posterior, he]

theorem gameCondition_relativeEntropy_le (μ : Games.FiniteDistribution α) (event : α → Bool)
    (positive : 0 < μ.probability event) :
    relativeEntropy (μ.condition event positive).weight μ.weight ≤
      Real.log (1 / μ.probability event) := by
  rw [gameCondition_weight]
  apply posterior_relativeEntropy_le μ.weight (fun a => if event a then 1 else 0)
    (gameLaw_isProbability μ)
  · intro a
    cases event a <;> norm_num
  · intro a
    cases event a <;> norm_num
  · exact positive
  · unfold Games.FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro a _
    cases event a <;> simp

end IndependentSetsGames.Foundations.Information

end OAI
