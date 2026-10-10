import Mathlib
import OAI.Computability.MinUncut.Games.Sampling

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution

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
end MinUncutGames.Foundations.Games.FiniteDistribution

namespace MinUncutGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

def condition (μ : FiniteDistribution Ω) (given : Ω → Bool)
    (positive : 0 < μ.probability given) : FiniteDistribution Ω where
  weight x := if given x then μ.weight x / μ.probability given else 0
  nonnegative x := by
    split
    · exact div_nonneg (μ.nonnegative x) positive.le
    · exact le_rfl
  normalized := by
    calc
      _ = (∑ x, if given x then μ.weight x else 0) / μ.probability given := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : given x = true <;> simp [hx]
      _ = 1 := div_self (ne_of_gt positive)

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

theorem probability_and_le_left (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.1

theorem probability_and_le_right (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event' := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.2

theorem probability_and_eq_zero_of_probability_eq_zero (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (zero : μ.probability given = 0) :
    μ.probability (fun x => given x && event x) = 0 := by
  apply le_antisymm
  · exact (μ.probability_and_le_left given event).trans_eq zero
  · exact μ.probability_nonnegative _

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedWins_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n) :
    G.selectedWins strategy (insert coordinate selected) =
      fun questions =>
        G.selectedWins strategy selected questions && G.coordinateWin strategy coordinate questions := by
  classical
  funext questions
  apply Bool.eq_iff_iff.mpr
  simp [selectedWins, and_comm]

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

theorem selectedSuccess_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : 0 ≤ G.selectedSuccess strategy selected :=
  (G.repetition n).questions.probability_nonnegative _

theorem selectedSuccess_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : G.selectedSuccess strategy selected ≤ 1 :=
  (G.repetition n).questions.probability_le_one _

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

theorem selectedSuccess_univ (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy Finset.univ = (G.repetition n).success strategy := by
  rw [selectedSuccess, G.selectedWins_univ]
  rfl

theorem selectedSuccess_antitone (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Antitone (G.selectedSuccess strategy) := by
  intro selected selected' h
  exact G.selectedWins_mono strategy h

theorem selectedSuccess_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n)
    (positive : 0 < G.selectedSuccess strategy selected) :
    G.selectedSuccess strategy (insert coordinate selected) =
      G.selectedSuccess strategy selected *
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          (G.coordinateWin strategy coordinate) := by
  unfold selectedSuccess
  rw [G.selectedWins_insert]
  exact (G.repetition n).questions.probability_inter_eq_mul_conditional _ _ positive

theorem selectedSuccess_insert_eq_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n)
    (zero : G.selectedSuccess strategy selected = 0) :
    G.selectedSuccess strategy (insert coordinate selected) = 0 := by
  apply le_antisymm
  · exact (G.selectedSuccess_antitone strategy (Finset.subset_insert coordinate selected)).trans_eq zero
  · exact G.selectedSuccess_nonnegative _ _

end Game

end

end MinUncutGames.Foundations.Games

namespace MinUncutGames.Foundations.Information

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

end MinUncutGames.Foundations.Information

end OAI
