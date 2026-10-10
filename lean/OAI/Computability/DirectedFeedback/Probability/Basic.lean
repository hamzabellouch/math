import Mathlib

namespace OAI


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

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

end Game

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

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

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

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
end
end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

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

end
end DFVSGames.Foundations.Games.FiniteDistribution


namespace DFVSGames.Repetition

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

def IsProjection (G : Game Q₁ Q₂ A₁ A₂) : Prop :=
  ∀ x y a b b', G.accepts x y a b = true →
    G.accepts x y a b' = true → b = b'

theorem IsProjection.of_accepts_iff (G : Game Q₁ Q₂ A₁ A₂)
    (project : Q₁ → Q₂ → A₁ → A₂)
    (h : ∀ x y a b, G.accepts x y a b = true ↔ project x y a = b) :
    IsProjection G := by
  intro x y a b b' hb hb'
  exact ((h x y a b).mp hb).symm.trans ((h x y a b').mp hb')

theorem IsProjection.repetition {G : Game Q₁ Q₂ A₁ A₂}
    (hG : IsProjection G) (n : Nat) : IsProjection (G.repetition n) := by
  intro x y a b b' hb hb'
  have h₁ := (G.repetition_accepts_iff n x y a b).mp hb
  have h₂ := (G.repetition_accepts_iff n x y a b').mp hb'
  funext i
  exact hG (x i) (y i) (a i) (b i) (b' i) (h₁ i) (h₂ i)

def ofProjection (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) : Game Q₁ Q₂ A₁ A₂ := by
  classical
  exact { questions := questions, accepts := fun x y a b => decide (project x y a = b) }

@[simp] theorem ofProjection_accepts_iff
    (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) (x : Q₁) (y : Q₂) (a : A₁) (b : A₂) :
    (ofProjection questions project).accepts x y a b = true ↔ project x y a = b := by
  classical
  simp [ofProjection]

theorem ofProjection_isProjection (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) : IsProjection (ofProjection questions project) :=
  IsProjection.of_accepts_iff _ project (ofProjection_accepts_iff questions project)

def productQuestionEquiv :
    ((Q₁ × Q₂) × (R₁ × R₂)) ≃ ((Q₁ × R₁) × (Q₂ × R₂)) where
  toFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def product (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂) :
    Game (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  questions := (G.questions.product H.questions).transport productQuestionEquiv
  accepts x y a b := G.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2

@[simp] theorem product_question_weight
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (q : (Q₁ × R₁) × (Q₂ × R₂)) :
    (product G H).questions.weight q =
      G.questions.weight (q.1.1, q.2.1) * H.questions.weight (q.1.2, q.2.2) := rfl

@[simp] theorem product_accepts_iff
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (x : Q₁ × R₁) (y : Q₂ × R₂) (a : A₁ × B₁) (b : A₂ × B₂) :
    (product G H).accepts x y a b = true ↔
      G.accepts x.1 y.1 a.1 b.1 = true ∧ H.accepts x.2 y.2 a.2 b.2 = true := by
  simp [product]

theorem IsProjection.product {G : Game Q₁ Q₂ A₁ A₂} {H : Game R₁ R₂ B₁ B₂}
    (hG : IsProjection G) (hH : IsProjection H) : IsProjection (product G H) := by
  intro x y a b b' hb hb'
  have h₁ := (product_accepts_iff G H x y a b).mp hb
  have h₂ := (product_accepts_iff G H x y a b').mp hb'
  exact Prod.ext (hG _ _ _ _ _ h₁.1 h₂.1) (hH _ _ _ _ _ h₁.2 h₂.2)

def productStrategy (s : Strategy Q₁ Q₂ A₁ A₂) (t : Strategy R₁ R₂ B₁ B₂) :
    Strategy (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) :=
  (fun q => (s.1 q.1, t.1 q.2), fun q => (s.2 q.1, t.2 q.2))

theorem success_productStrategy (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) (t : Strategy R₁ R₂ B₁ B₂) :
    (product G H).success (productStrategy s t) = G.success s * H.success t := by
  unfold Game.success
  change ((G.questions.product H.questions).transport productQuestionEquiv).probability _ = _
  rw [FiniteDistribution.probability_transport]
  change (G.questions.product H.questions).probability
    (fun q => G.wins s q.1 && H.wins t q.2) = _
  simp only [FiniteDistribution.probability, FiniteDistribution.product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : G.wins s q = true <;>
    by_cases hr : H.wins t r = true <;> simp [hq, hr]

theorem mul_value_le_product_value [Nonempty A₁] [Nonempty A₂]
    [Nonempty B₁] [Nonempty B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂) :
    G.value * H.value ≤ (product G H).value := by
  obtain ⟨s, hs⟩ := G.exists_optimal_strategy
  obtain ⟨t, ht⟩ := H.exists_optimal_strategy
  rw [← hs, ← ht, ← success_productStrategy]
  exact (product G H).success_le_value (productStrategy s t)

end
end DFVSGames.Repetition

end OAI
