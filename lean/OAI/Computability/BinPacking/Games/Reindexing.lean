import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Games

open scoped BigOperators

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_le_one (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.probability event ≤ 1 := by
  rw [← μ.normalized]
  apply Finset.sum_le_sum
  intro x _
  split
  · exact le_rfl
  · exact μ.nonnegative x

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

theorem probability_mono (μ : FiniteDistribution Ω) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    μ.probability event ≤ μ.probability event' := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · simp [hx, h x hx]
  · simp [hx]
    split
    · exact μ.nonnegative x
    · exact le_rfl

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

theorem probability_transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ)
    (event : Γ → Bool) :
    (μ.transport equiv).probability event = μ.probability (fun x => event (equiv x)) := by
  unfold probability transport
  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => by simp)

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

theorem probability_iid_all (μ : FiniteDistribution Ω) (event : Ω → Bool) (n : Nat) :
    (μ.iid n).probability (fun x => decide (∀ i, event (x i) = true)) =
      μ.probability event ^ n := by
  classical
  unfold probability iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  by_cases h : ∀ i, event (x i) = true
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end FiniteDistribution

abbrev Strategy (Q₁ Q₂ A₁ A₂ : Type*) := (Q₁ → A₁) × (Q₂ → A₂)

structure Game (Q₁ Q₂ A₁ A₂ : Type*) [Fintype Q₁] [Fintype Q₂]
    [Fintype A₁] [Fintype A₂] where
  questions : FiniteDistribution (Q₁ × Q₂)
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool

namespace Game

section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def wins (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂)
    (questions : Q₁ × Q₂) : Bool :=
  G.accepts questions.1 questions.2 (strategy.1 questions.1) (strategy.2 questions.2)

def success (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.questions.probability (G.wins strategy)

theorem success_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : 0 ≤ G.success strategy :=
  G.questions.probability_nonnegative _

theorem success_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ 1 :=
  G.questions.probability_le_one _

def simulatedStrategy {R₁ R₂ B₁ B₂ : Type*}
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (strategy : Strategy R₁ R₂ B₁ B₂) : Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => answerMap₁ x (strategy.1 (questionMap₁ x)),
   fun y => answerMap₂ y (strategy.2 (questionMap₂ y)))

theorem success_le_of_localSimulation {R₁ R₂ B₁ B₂ : Type*}
    [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (questionLaw : H.questions =
      G.questions.pushforward (fun q => (questionMap₁ q.1, questionMap₂ q.2)))
    (acceptance : ∀ x y a b,
      H.accepts (questionMap₁ x) (questionMap₂ y) a b = true →
      G.accepts x y (answerMap₁ x a) (answerMap₂ y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤
      G.success (simulatedStrategy questionMap₁ questionMap₂ answerMap₁ answerMap₂ strategy) := by
  unfold success
  rw [questionLaw, FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro questions h
  exact acceptance questions.1 questions.2 _ _ h

def tupleQuestionEquiv (n : Nat) :
    (Fin n → Q₁ × Q₂) ≃ (Fin n → Q₁) × (Fin n → Q₂) where
  toFun questions := (fun i => (questions i).1, fun i => (questions i).2)
  invFun questions := fun i => (questions.1 i, questions.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { questions := (G.questions.iid n).transport (tupleQuestionEquiv n)
      accepts := fun x y a b => decide (∀ i, G.accepts (x i) (y i) (a i) (b i) = true) }

def repeatStrategy (strategy : Strategy Q₁ Q₂ A₁ A₂) (n : Nat) :
    Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) :=
  (fun x i => strategy.1 (x i), fun y i => strategy.2 (y i))

theorem success_repeatStrategy (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) (n : Nat) :
    (G.repetition n).success (repeatStrategy strategy n) = G.success strategy ^ n := by
  unfold success
  change ((G.questions.iid n).transport (tupleQuestionEquiv n)).probability _ = _
  rw [FiniteDistribution.probability_transport]
  exact G.questions.probability_iid_all (G.wins strategy) n

@[simp] theorem repetition_question_weight (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition n).questions.weight questions =
      ∏ i, G.questions.weight (questions.1 i, questions.2 i) := rfl

@[simp] theorem repetition_accepts_iff (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (G.repetition n).accepts x y a b = true ↔
      ∀ i, G.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

def coordinateWin (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (coordinate : Fin n) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool :=
  G.accepts (questions.1 coordinate) (questions.2 coordinate)
    (strategy.1 questions.1 coordinate) (strategy.2 questions.2 coordinate)

def selectedWins (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool := by
  classical
  exact decide (∀ i ∈ selected, G.coordinateWin strategy i questions = true)

theorem selectedWins_mono (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {selected selected' : Finset (Fin n)} (h : selected ⊆ selected') :
    (G.repetition n).questions.probability (G.selectedWins strategy selected') ≤
      (G.repetition n).questions.probability (G.selectedWins strategy selected) := by
  apply FiniteDistribution.probability_mono
  intro questions hwin
  simp only [selectedWins, decide_eq_true_eq] at hwin ⊢
  intro i hi
  exact hwin i (h hi)

@[simp] theorem selectedWins_empty (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins strategy ∅ questions = true := by
  simp [selectedWins]

theorem selectedWins_univ (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedWins strategy Finset.univ = (G.repetition n).wins strategy := by
  classical
  funext questions
  simp [selectedWins, coordinateWin, repetition, wins]

end

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : Game Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

theorem exists_optimal_strategy (G : Game Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

theorem value_nonnegative (G : Game Q₁ Q₂ A₁ A₂) : 0 ≤ G.value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h]
  exact G.success_nonnegative strategy

theorem value_le_one (G : Game Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

theorem randomized_success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    {Seed : Type*} [Fintype Seed] (seedLaw : FiniteDistribution Seed)
    (strategies : Seed → Strategy Q₁ Q₂ A₁ A₂) :
    seedLaw.expectation (fun seed => G.success (strategies seed)) ≤ G.value := by
  unfold FiniteDistribution.expectation
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * G.value := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (G.success_le_value _) (seedLaw.nonnegative seed)
    _ = G.value := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

omit [Nonempty A₁] [Nonempty A₂] in
theorem success_repetition_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin 0 → Q₁) (Fin 0 → Q₂) (Fin 0 → A₁) (Fin 0 → A₂)) :
    (G.repetition 0).success strategy = 1 := by
  have h : (G.repetition 0).wins strategy = fun _ => true := by
    funext questions
    simp [wins, repetition]
  unfold success
  rw [h, FiniteDistribution.probability_true]

@[simp] theorem value_repetition_zero (G : Game Q₁ Q₂ A₁ A₂) :
    (G.repetition 0).value = 1 := by
  obtain ⟨strategy, h⟩ := (G.repetition 0).exists_optimal_strategy
  rw [← h]
  exact G.success_repetition_zero strategy

theorem pow_value_le_repetition_value (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    G.value ^ n ≤ (G.repetition n).value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h, ← G.success_repeatStrategy strategy n]
  exact (G.repetition n).success_le_value (repeatStrategy strategy n)

theorem value_le_of_localSimulation {R₁ R₂ B₁ B₂ : Type*}
    [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
    [Nonempty B₁] [Nonempty B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (questionLaw : H.questions =
      G.questions.pushforward (fun q => (questionMap₁ q.1, questionMap₂ q.2)))
    (acceptance : ∀ x y a b,
      H.accepts (questionMap₁ x) (questionMap₂ y) a b = true →
      G.accepts x y (answerMap₁ x a) (answerMap₂ y b) = true) :
    H.value ≤ G.value := by
  apply (H.value_le_iff _).2
  intro strategy
  exact (G.success_le_of_localSimulation H questionMap₁ questionMap₂
    answerMap₁ answerMap₂ questionLaw acceptance strategy).trans (G.success_le_value _)

end Game

end BinPackingGames.Foundations.Games

namespace BinPackingGames.Foundations.Games.FiniteDistribution

section

open scoped BigOperators

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

def mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) : FiniteDistribution Ω where
  weight x := ∑ seed, seedLaw.weight seed * (laws seed).weight x
  nonnegative x := Finset.sum_nonneg fun seed _ =>
    mul_nonneg (seedLaw.nonnegative seed) ((laws seed).nonnegative x)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (laws _).normalized, mul_one]
    exact seedLaw.normalized

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

theorem probability_mixture_le (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) (bound : ℝ)
    (h : ∀ seed, (laws seed).probability event ≤ bound) :
    (seedLaw.mixture laws).probability event ≤ bound := by
  rw [probability_mixture]
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * bound :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (h seed) (seedLaw.nonnegative seed)
    _ = bound := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end

open scoped BigOperators

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

end BinPackingGames.Foundations.Games.FiniteDistribution

namespace BinPackingGames.Foundations.Games

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

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

theorem table_eval_pushforward [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (q₀ : Q) :
    (table responses).pushforward (fun answers => answers q₀) = responses q₀ := by
  classical
  apply eq_of_weight_eq
  intro a
  calc
    _ = (table responses).expectation
        (fun answers => if answers q₀ = a then 1 else 0) := by
      simp [pushforward, expectation, mul_ite]
    _ = (responses q₀).expectation (fun b => if b = a then 1 else 0) :=
      expectation_table_eval responses q₀ (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [expectation, mul_ite]

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def responseTableLaw (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    FiniteDistribution (Strategy Q₁ Q₂ A₁ A₂) := by
  classical
  exact (FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)

def stochasticSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.questions.expectation (fun q =>
    (responses₁ q.1).expectation (fun a =>
      (responses₂ q.2).expectation (fun b =>
        if G.accepts q.1 q.2 a b then 1 else 0)))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem success_eq_question_expectation (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    G.success strategy = G.questions.expectation
      (fun q => if G.wins strategy q then 1 else 0) := by
  simp [success, FiniteDistribution.probability,
    FiniteDistribution.expectation, mul_ite]

theorem table_success_eq_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    (responseTableLaw responses₁ responses₂).expectation G.success =
      G.stochasticSuccess responses₁ responses₂ := by
  classical
  unfold stochasticSuccess
  calc
    _ = (responseTableLaw responses₁ responses₂).expectation
        (fun strategy => G.questions.expectation
          (fun q => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_congr _ (G.success_eq_question_expectation)
    _ = G.questions.expectation (fun q =>
        (responseTableLaw responses₁ responses₂).expectation
          (fun strategy => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro q
      rw [responseTableLaw, FiniteDistribution.expectation_product]
      change (FiniteDistribution.table responses₁).expectation
        (fun answers₁ => (FiniteDistribution.table responses₂).expectation
          (fun answers₂ =>
            if G.accepts q.1 q.2 (answers₁ q.1) (answers₂ q.2) then 1 else 0)) = _
      calc
        _ = (FiniteDistribution.table responses₁).expectation
            (fun answers₁ => (responses₂ q.2).expectation
              (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then 1 else 0)) := by
          apply FiniteDistribution.expectation_congr
          intro answers₁
          exact FiniteDistribution.expectation_table_eval responses₂ q.2
            (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then (1 : ℝ) else 0)
        _ = _ := FiniteDistribution.expectation_table_eval responses₁ q.1
          (fun a => (responses₂ q.2).expectation
            (fun b => if G.accepts q.1 q.2 a b then (1 : ℝ) else 0))

variable [Nonempty A₁] [Nonempty A₂]

theorem stochasticSuccess_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    G.stochasticSuccess responses₁ responses₂ ≤ G.value := by
  classical
  rw [← G.table_success_eq_stochastic]
  exact G.randomized_success_le_value (responseTableLaw responses₁ responses₂) id

theorem exists_deterministic_ge_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂,
      G.stochasticSuccess responses₁ responses₂ ≤ G.success strategy := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  refine ⟨strategy, ?_⟩
  rw [h]
  exact G.stochasticSuccess_le_value responses₁ responses₂
end Game
end BinPackingGames.Foundations.Games

namespace BinPackingGames.Foundations.Games.FiniteDistribution
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

end BinPackingGames.Foundations.Games.FiniteDistribution

namespace BinPackingGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

def reindexEquiv {ι κ Ω : Type*} (e : κ ≃ ι) : (ι → Ω) ≃ (κ → Ω) where
  toFun f := f ∘ e
  invFun g := g ∘ e.symm
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

theorem table_const_reindex {ι κ Ω : Type*}
    [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
    (μ : FiniteDistribution Ω) (e : κ ≃ ι) :
    (table (fun _ : ι => μ)).pushforward (fun f => f ∘ e) =
      table (fun _ : κ => μ) := by
  classical
  change (table (fun _ : ι => μ)).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : ι, μ.weight (g (e.symm i))) = ∏ k : κ, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

theorem iid_reindex {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {n m : Nat} (e : Fin m ≃ Fin n) :
    (μ.iid n).pushforward (fun f => f ∘ e) = μ.iid m := by
  classical
  change (μ.iid n).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : Fin n, μ.weight (g (e.symm i))) = ∏ k : Fin m, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

theorem probability_reindex_of_weight {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (e : Ω ≃ Γ)
    (hweight : ∀ x, ν.weight (e x) = μ.weight x) (event : Γ → Bool) :
    ν.probability event = μ.probability (fun x => event (e x)) := by
  classical
  change (∑ y, if event y then ν.weight y else 0) =
    ∑ x, if event (e x) then μ.weight x else 0
  rw [← e.sum_comp (fun y => if event y then ν.weight y else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [hweight]

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def questionReindexEquiv {n m : Nat} (e : Fin m ≃ Fin n) :
    ((Fin n → Q₁) × (Fin n → Q₂)) ≃ ((Fin m → Q₁) × (Fin m → Q₂)) :=
  Equiv.prodCongr (FiniteDistribution.reindexEquiv e)
    (FiniteDistribution.reindexEquiv e)

def reindexStrategy {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Strategy (Fin m → Q₁) (Fin m → Q₂) (Fin m → A₁) (Fin m → A₂) :=
  (fun x i => s.1 (x ∘ e.symm) (e i),
   fun y i => s.2 (y ∘ e.symm) (e i))

theorem repetition_question_weight_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition m).questions.weight (questionReindexEquiv e q) =
      (G.repetition n).questions.weight q := by
  classical
  rw [repetition_question_weight, repetition_question_weight]
  change (∏ i : Fin m, G.questions.weight (q.1 (e i), q.2 (e i))) =
    ∏ j : Fin n, G.questions.weight (q.1 j, q.2 j)
  exact e.prod_comp (fun j => G.questions.weight (q.1 j, q.2 j))

theorem repetition_questions_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n) :
    (G.repetition n).questions.pushforward (questionReindexEquiv e) =
      (G.repetition m).questions := by
  classical
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  change (G.repetition n).questions.weight ((questionReindexEquiv e).symm q) =
    (G.repetition m).questions.weight q
  have h := repetition_question_weight_reindex G e ((questionReindexEquiv e).symm q)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem coordinateWin_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (i : Fin m) (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.coordinateWin (reindexStrategy e s) i (questionReindexEquiv e q) =
      G.coordinateWin s (e i) q := by
  have h₁ : (fun j : Fin n => q.1 (e (e.symm j))) = q.1 := by
    funext j
    rw [e.apply_symm_apply]
  have h₂ : (fun j : Fin n => q.2 (e (e.symm j))) = q.2 := by
    funext j
    rw [e.apply_symm_apply]
  change G.accepts (q.1 (e i)) (q.2 (e i))
      (s.1 (fun j => q.1 (e (e.symm j))) (e i))
      (s.2 (fun j => q.2 (e (e.symm j))) (e i)) =
    G.accepts (q.1 (e i)) (q.2 (e i)) (s.1 q.1 (e i)) (s.2 q.2 (e i))
  rw [h₁, h₂]

theorem selectedWins_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (S : Finset (Fin m)) (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins (reindexStrategy e s) S (questionReindexEquiv e q) =
      G.selectedWins s (S.map e.toEmbedding) q := by
  classical
  unfold selectedWins
  congr 1
  apply propext
  constructor
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    have hw := h i hi
    rw [coordinateWin_reindex] at hw
    exact hw
  · intro h i hi
    rw [coordinateWin_reindex]
    exact h (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)

theorem selectedSuccess_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (S : Finset (Fin m)) :
    G.selectedSuccess (reindexStrategy e s) S =
      G.selectedSuccess s (S.map e.toEmbedding) := by
  classical
  unfold selectedSuccess
  rw [FiniteDistribution.probability_reindex_of_weight
    (G.repetition n).questions (G.repetition m).questions (questionReindexEquiv e)
    (repetition_question_weight_reindex G e)]
  congr 1
  funext q
  exact selectedWins_reindex G e s S q

theorem repetition_success_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    (G.repetition m).success (reindexStrategy e s) =
      (G.repetition n).success s := by
  classical
  have huniv : (Finset.univ : Finset (Fin m)).map e.toEmbedding = Finset.univ := by
    ext j
    constructor
    · intro _
      exact Finset.mem_univ j
    · intro _
      exact Finset.mem_map.mpr ⟨e.symm j, Finset.mem_univ _, e.apply_symm_apply j⟩
  have h := selectedSuccess_reindex G e s Finset.univ
  rw [huniv, selectedSuccess_univ, selectedSuccess_univ] at h
  exact h

end Game
end BinPackingGames.Foundations.Games

end

end OAI
