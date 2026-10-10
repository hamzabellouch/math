import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

structure OccurrenceGame (E Q₁ Q₂ A₁ A₂ : Type*)
    [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] where
  occurrences : FiniteDistribution E
  left : E → Q₁
  right : E → Q₂
  accepts : E → A₁ → A₂ → Bool

namespace OccurrenceGame

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def ofProjection (μ : FiniteDistribution E) (left : E → Q₁) (right : E → Q₂)
    (projection : E → A₁ → A₂) : OccurrenceGame E Q₁ Q₂ A₁ A₂ := by
  classical
  exact
    { occurrences := μ
      left := left
      right := right
      accepts := fun e a b => decide (projection e a = b) }

def endpoints (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (e : E) : Q₁ × Q₂ :=
  (G.left e, G.right e)

def wins (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) (e : E) : Bool :=
  G.accepts e (strategy.1 (G.left e)) (strategy.2 (G.right e))

def success (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.occurrences.probability (G.wins strategy)

theorem success_nonnegative (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : 0 ≤ G.success strategy :=
  G.occurrences.probability_nonnegative _

theorem success_le_one (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ 1 :=
  G.occurrences.probability_le_one _

structure EndpointPresentation (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) where
  predicate : Q₁ → Q₂ → A₁ → A₂ → Bool
  agrees : ∀ e a b, G.accepts e a b = predicate (G.left e) (G.right e) a b

def EndpointDetermined (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : Prop :=
  ∀ e e', G.left e = G.left e' → G.right e = G.right e' →
    ∀ a b, G.accepts e a b = G.accepts e' a b

private def chosenEndpointPredicate (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (x : Q₁) (y : Q₂) (a : A₁) (b : A₂) : Bool := by
  classical
  exact if h : ∃ e, G.left e = x ∧ G.right e = y then
    G.accepts (Classical.choose h) a b
  else false

def presentationOfDetermined (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (h : G.EndpointDetermined) : G.EndpointPresentation where
  predicate := chosenEndpointPredicate G
  agrees e a b := by
    have hex : ∃ e', G.left e' = G.left e ∧ G.right e' = G.right e :=
      ⟨e, rfl, rfl⟩
    simp only [chosenEndpointPredicate, dite_eq_left hex]
    exact h e (Classical.choose hex) (Classical.choose_spec hex).1.symm
      (Classical.choose_spec hex).2.symm a b

theorem EndpointPresentation.determined (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) : G.EndpointDetermined := by
  intro e e' hl hr a b
  rw [p.agrees, p.agrees, hl, hr]

def toGame (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) : Game Q₁ Q₂ A₁ A₂ where
  questions := G.occurrences.pushforward G.endpoints
  accepts := p.predicate

@[simp] theorem toGame_success (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (G.toGame p).success strategy = G.success strategy := by
  unfold Game.success OccurrenceGame.success toGame
  rw [FiniteDistribution.probability_pushforward]
  congr 1
  funext e
  exact (p.agrees e (strategy.1 (G.left e)) (strategy.2 (G.right e))).symm

def repetition (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (n : Nat) :
    OccurrenceGame (Fin n → E) (Fin n → Q₁) (Fin n → Q₂)
      (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { occurrences := G.occurrences.iid n
      left := fun e i => G.left (e i)
      right := fun e i => G.right (e i)
      accepts := fun e a b => decide (∀ i, G.accepts (e i) (a i) (b i) = true) }

def EndpointPresentation.repetition (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (n : Nat) : (G.repetition n).EndpointPresentation := by
  classical
  exact
    { predicate := fun x y a b => decide (∀ i, p.predicate (x i) (y i) (a i) (b i) = true)
      agrees := by
        intro e a b
        simp only [OccurrenceGame.repetition, p.agrees] }

theorem toGame_repetition_questions (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (n : Nat) :
    ((G.toGame p).repetition n).questions =
      (G.occurrences.iid n).pushforward (G.repetition n).endpoints := by
  change ((G.occurrences.pushforward G.endpoints).iid n).transport
    (Game.tupleQuestionEquiv n) = _
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.transport_eq_pushforward,
    FiniteDistribution.pushforward_comp]
  rfl

theorem toGame_repetition_success (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    ((G.toGame p).repetition n).success strategy = (G.repetition n).success strategy := by
  classical
  unfold Game.success OccurrenceGame.success
  rw [G.toGame_repetition_questions p n, FiniteDistribution.probability_pushforward]
  congr 1
  funext e
  simp only [Game.wins, Game.repetition, toGame, OccurrenceGame.repetition,
    endpoints, wins, p.agrees]
  rfl


variable [Nonempty A₁] [Nonempty A₂]

def value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

theorem exists_optimal_strategy (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

theorem value_nonnegative (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : 0 ≤ G.value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h]
  exact G.success_nonnegative strategy

theorem value_le_one (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

theorem randomized_success_le_value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
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

@[simp] theorem toGame_value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) : (G.toGame p).value = G.value := by
  apply le_antisymm
  · apply ((G.toGame p).value_le_iff _).2
    intro strategy
    rw [G.toGame_success p strategy]
    exact G.success_le_value strategy
  · apply (G.value_le_iff _).2
    intro strategy
    rw [← G.toGame_success p strategy]
    exact (G.toGame p).success_le_value strategy

theorem toGame_repetition_value (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (p : G.EndpointPresentation) (n : Nat) :
    ((G.toGame p).repetition n).value = (G.repetition n).value := by
  apply le_antisymm
  · apply (((G.toGame p).repetition n).value_le_iff _).2
    intro strategy
    rw [G.toGame_repetition_success p n strategy]
    exact (G.repetition n).success_le_value strategy
  · apply ((G.repetition n).value_le_iff _).2
    intro strategy
    rw [← G.toGame_repetition_success p n strategy]
    exact ((G.toGame p).repetition n).success_le_value strategy

end OccurrenceGame
end
end PerfectCompleteness

end OAI
