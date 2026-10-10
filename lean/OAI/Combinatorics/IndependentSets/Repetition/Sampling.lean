import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Value

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Games.FiniteDistribution
open scoped BigOperators

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end IndependentSetsGames.Foundations.Games.FiniteDistribution

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

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

end IndependentSetsGames.Foundations.Games

end

end OAI
