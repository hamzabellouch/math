import Mathlib
import OAI.Computability.MaxCut.Games.LabelBound

namespace OAI

/-! Exact interfaces between the information vectors and finite game laws. -/

namespace MaxCutGames.Foundations.Information

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

end MaxCutGames.Foundations.Information

end OAI
