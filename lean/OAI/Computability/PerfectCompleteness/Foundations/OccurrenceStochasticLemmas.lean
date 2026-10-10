import OAI.Computability.PerfectCompleteness.Reduction.OccurrenceGame
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI


namespace PerfectCompleteness.OccurrenceGame

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def stochasticSuccess (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.occurrences.expectation (fun e =>
    (responses₁ (G.left e)).expectation (fun a =>
      (responses₂ (G.right e)).expectation
        (fun b => if G.accepts e a b then 1 else 0)))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem success_eq_occurrence_expectation (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    G.success strategy = G.occurrences.expectation
      (fun e => if G.wins strategy e then 1 else 0) := by
  simp [success, FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]

theorem table_success_eq_stochastic (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    ((FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)).expectation
      G.success = G.stochasticSuccess responses₁ responses₂ := by
  classical
  unfold stochasticSuccess
  calc
    _ = ((FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)).expectation
        (fun strategy => G.occurrences.expectation
          (fun e => if G.wins strategy e then 1 else 0)) :=
      FiniteDistribution.expectation_congr _ G.success_eq_occurrence_expectation
    _ = G.occurrences.expectation (fun e =>
        ((FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)).expectation
          (fun strategy => if G.wins strategy e then 1 else 0)) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro e
      rw [FiniteDistribution.expectation_product]
      change (FiniteDistribution.table responses₁).expectation
        (fun answers₁ => (FiniteDistribution.table responses₂).expectation
          (fun answers₂ =>
            if G.accepts e (answers₁ (G.left e)) (answers₂ (G.right e)) then 1 else 0)) = _
      calc
        _ = (FiniteDistribution.table responses₁).expectation
            (fun answers₁ => (responses₂ (G.right e)).expectation
              (fun b => if G.accepts e (answers₁ (G.left e)) b then 1 else 0)) := by
          apply FiniteDistribution.expectation_congr
          intro answers₁
          exact FiniteDistribution.expectation_table_eval responses₂ (G.right e)
            (fun b => if G.accepts e (answers₁ (G.left e)) b then (1 : ℝ) else 0)
        _ = _ := FiniteDistribution.expectation_table_eval responses₁ (G.left e)
          (fun a => (responses₂ (G.right e)).expectation
            (fun b => if G.accepts e a b then (1 : ℝ) else 0))

theorem stochasticSuccess_le_value [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    G.stochasticSuccess responses₁ responses₂ ≤ G.value := by
  rw [← G.table_success_eq_stochastic]
  exact G.randomized_success_le_value
    ((FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)) id

end
end PerfectCompleteness.OccurrenceGame



namespace PerfectCompleteness.OccurrenceVertexEmbedding

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {E Q₁ Q₂ N₁ N₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype N₁] [Fintype N₂]
  [Fintype A₁] [Fintype A₂]

def rename (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) :
    OccurrenceGame E N₁ N₂ A₁ A₂ where
  occurrences := G.occurrences
  left e := left (G.left e)
  right e := right (G.right e)
  accepts := G.accepts

def restrict (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (strategy : Strategy N₁ N₂ A₁ A₂) :
    Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => strategy.1 (left x), fun y => strategy.2 (right y))

@[simp] theorem wins_restrict (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (strategy : Strategy N₁ N₂ A₁ A₂) (e : E) :
    (rename G left right).wins strategy e = G.wins (restrict left right strategy) e := rfl

@[simp] theorem success_restrict (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (strategy : Strategy N₁ N₂ A₁ A₂) :
    (rename G left right).success strategy = G.success (restrict left right strategy) := rfl

def extend (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (defaultLeft : A₁) (defaultRight : A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : Strategy N₁ N₂ A₁ A₂ :=
  (Function.extend left strategy.1 (fun _ => defaultLeft),
    Function.extend right strategy.2 (fun _ => defaultRight))

omit [Fintype Q₁] [Fintype Q₂] [Fintype N₁] [Fintype N₂] [Fintype A₁] [Fintype A₂] in
@[simp] theorem restrict_extend (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂)
    (defaultLeft : A₁) (defaultRight : A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    restrict left right (extend left right defaultLeft defaultRight strategy) = strategy := by
  apply Prod.ext
  · funext x
    exact left.injective.extend_apply strategy.1 (fun _ => defaultLeft) x
  · funext y
    exact right.injective.extend_apply strategy.2 (fun _ => defaultRight) y

theorem success_extend (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) (defaultLeft : A₁) (defaultRight : A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (rename G left right).success (extend left right defaultLeft defaultRight strategy) =
      G.success strategy := by
  rw [success_restrict, restrict_extend]

theorem value_eq [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (left : Q₁ ↪ N₁) (right : Q₂ ↪ N₂) :
    (rename G left right).value = G.value := by
  apply le_antisymm
  · apply ((rename G left right).value_le_iff _).2
    intro strategy
    rw [success_restrict]
    exact G.success_le_value _
  · apply (G.value_le_iff _).2
    intro strategy
    let s := extend left right (Classical.choice inferInstance) (Classical.choice inferInstance)
      strategy
    have h := (rename G left right).success_le_value s
    simpa only [s, success_extend] using h

end
end PerfectCompleteness.OccurrenceVertexEmbedding

end OAI
