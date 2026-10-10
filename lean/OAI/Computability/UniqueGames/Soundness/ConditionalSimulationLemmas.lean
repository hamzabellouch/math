import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Soundness.ConditionalLocality
import OAI.Computability.UniqueGames.Soundness.ConditionalReindex
import OAI.Computability.UniqueGames.Soundness.RawTargetLawLemmas

namespace OAI

section

/-!
The actual local simulation in Lemma 6.8 after fixing H. These reconstruction
maps consume only the first player's occurrence tuple or the second player's
name tuple. Its winning-event containment is proved from the concrete equation
and named-projection predicates.
-/

namespace UniqueGamesTheorem.Soundness.ConditionalSimulation

open Foundations.Games ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

instance firstInputFintype {P R O : Type} [Fintype P] [Fintype R] [Fintype O] :
    Fintype (ZeroInformation.FirstInput P R O) := by
  classical
  exact Fintype.ofEquiv ((P → O) × ZeroInformation.FirstRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

instance secondInputFintype {P R O N : Type}
    [Fintype P] [Fintype R] [Fintype O] [Fintype N] :
    Fintype (ZeroInformation.SecondInput P R O N) := by
  classical
  exact Fintype.ofEquiv ((P → Sum O N) × ZeroInformation.SecondRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

def incidenceGame {O N : Type} [Fintype O] [Fintype N]
    (g : Incidence O N) (mu : FiniteDistribution (O × N)) :
    Foundations.Games.Game O N Triple Bool :=
  Simulation.weightedGame ⟨g.namedAccepts⟩ mu

def actualLocalSimulation
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma)) :
    IncidenceExtraction.LocalSimulation
      (Simulation.predicateGame ((incidenceGame g mu).repetition (zeroSet J gamma).card))
      (ActualProjection.predicateGame (R := R) g (membershipBool J)) where
  questionA qa := localFirstFromH J g.name gamma observed reference
    (fun j => qa (enumerate.symm j))
  questionB qb := localSecondFromH J g.name gamma observed reference
    (fun j => qb (enumerate.symm j))
  answerA _ answer i := answer.2 (enumerate i).val
  answerB _ answer i := answer.2.2 (enumerate i).val
  sound := by
    classical
    intro qa qb answerA answerB haccept
    change ((incidenceGame g mu).repetition (zeroSet J gamma).card).accepts _ _ _ _ = true
    rw [Foundations.Games.Game.repetition_accepts_iff]
    intro i
    change decide (g.namedAccepts (qa i) (qb i)
      (answerA.2 (enumerate i).val) (answerB.2.2 (enumerate i).val)) = true
    rw [decide_eq_true_eq]
    have hj : (enumerate i).val ∈ J := zeroSet_subset J gamma (enumerate i).property
    have hsingle : membershipBool J (enumerate i).val = true := by
      simp [membershipBool, hj]
    have hname : (localSecondFromH J g.name gamma observed reference
        (fun j => qb (enumerate.symm j))).question (enumerate i).val = Sum.inr (qb i) := by
      simpa using localSecondFromH_question_inside J g.name gamma observed reference
        (fun j => qb (enumerate.symm j)) (enumerate i)
    have h := ActualProjection.accepts_implies_named_incidence g (membershipBool J)
      _ _ answerA answerB haccept (enumerate i).val hsingle (qb i) hname
    simpa only [localFirstFromH_question_inside, Equiv.symm_apply_apply] using h

theorem actual_conditioned_strategy_success_le_repeated_value
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : IncidenceExtraction.Strategies
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (Simulation.reconstructedGame
      ((incidenceGame g mu).repetition (zeroSet J gamma).card)
      (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (actualLocalSimulation J g gamma observed reference mu enumerate)).success
        (Simulation.strategyPair strategy) ≤
      ((incidenceGame g mu).repetition (zeroSet J gamma).card).value := by
  exact (Simulation.reconstructedGame_success_le
    ((incidenceGame g mu).repetition (zeroSet J gamma).card)
    (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualLocalSimulation J g gamma observed reference mu enumerate) strategy).trans
      (((incidenceGame g mu).repetition (zeroSet J gamma).card).success_le_value _)

end
end UniqueGamesTheorem.Soundness.ConditionalSimulation

end

section

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_probability_decide {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (event : Ω → Prop) [DecidablePred event] :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (event x)) =
      (∑ x, if event x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
  classical
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = _ := FiniteDistribution.expectation_uniform _

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev OuterStrategy := IncidenceExtraction.Strategies
  (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
  (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)

def actualWin (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) (draw : Draw P O) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualFirst J gamma draw) (actualSecond J g.name gamma draw)

def conditionedWinProbability (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) : ℝ := by
  classical
  letI : Nonempty (RawObservationFibre J g.name gamma observed) := ⟨reference⟩
  exact (FiniteDistribution.uniform (RawObservationFibre J g.name gamma observed)).probability
    (fun sample => decide (actualWin J g gamma strategy sample.val.2))

def reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (questions : Fin (zeroSet J gamma).card → O × N) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (localFirstFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).1))
    (localSecondFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).2))

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualWin_iff_reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (sample : RawObservationFibre J g.name gamma observed) :
    actualWin J g gamma strategy sample.val.2 ↔
      reconstructedEvent J g gamma observed reference e strategy
        (fun i => incidence g.name (sample.val.2 (e i).val)) := by
  unfold actualWin reconstructedEvent
  simp only [incidence, Equiv.apply_symm_apply]
  rw [localFirstFromH_correct J g.name gamma observed distinct reference sample,
    localSecondFromH_correct J g.name gamma observed reference sample]

omit [Fintype N] in
theorem conditionedWinProbability_eq_fresh (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    conditionedWinProbability J g gamma observed reference strategy =
      (∑ fresh : Fin (zeroSet J gamma).card → O × Fin 3,
        if reconstructedEvent J g gamma observed reference e strategy
          (fun i => incidence g.name (fresh i)) then (1:ℝ) else 0) /
          Fintype.card (Fin (zeroSet J gamma).card → O × Fin 3) := by
  classical
  let : Nonempty (RawObservationFibre J g.name gamma observed) := ⟨reference⟩
  have hpos : 0 < Fintype.card (RawObservationFibre J g.name gamma observed) := Fintype.card_pos
  unfold conditionedWinProbability
  rw [uniform_probability_decide]
  have hraw := raw_conditional_event_reindex_real J g.name gamma observed hpos
    (zeroSet J gamma).card e (reconstructedEvent J g gamma observed reference e strategy)
  simpa only [← actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct]
    using hraw

def incidenceLaw [Nonempty O] (g : Incidence O N) : FiniteDistribution (O × N) :=
  (FiniteDistribution.uniform (O × Fin 3)).pushforward (incidence g.name)

theorem reconstructed_success_eq_fresh_average [Nonempty O]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) :
    (Simulation.reconstructedGame
      ((incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card)
      (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (actualLocalSimulation J g gamma observed reference (incidenceLaw g) e)).success
        (Simulation.strategyPair strategy) =
      (∑ fresh : Fin (zeroSet J gamma).card → O × Fin 3,
        if reconstructedEvent J g gamma observed reference e strategy
          (fun i => incidence g.name (fresh i)) then (1:ℝ) else 0) /
          Fintype.card (Fin (zeroSet J gamma).card → O × Fin 3) := by
  classical
  let G := (incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card
  let outer := ActualProjection.predicateGame (R := R) g (membershipBool J)
  let r := actualLocalSimulation J g gamma observed reference (incidenceLaw g) e
  change (G.questions.pushforward (fun q => (r.questionA q.1, r.questionB q.2))).probability
    (fun q => decide (strategy.wins outer q.1 q.2)) = _
  rw [FiniteDistribution.probability_pushforward]
  change (((incidenceLaw g).iid (zeroSet J gamma).card).transport
    (Foundations.Games.Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability
      (fun q => decide (strategy.wins outer (r.questionA q.1) (r.questionB q.2))) = _
  rw [FiniteDistribution.probability_transport]
  unfold incidenceLaw
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.iid_uniform,
    FiniteDistribution.probability_pushforward]
  change (FiniteDistribution.uniform (Fin (zeroSet J gamma).card → O × Fin 3)).probability
    (fun fresh => decide (reconstructedEvent J g gamma observed reference e strategy
      (fun i => incidence g.name (fresh i)))) = _
  exact uniform_probability_decide _

/-- The actual finite observation-fibre probability is bounded by the genuine
    repeated incidence-game value. The sampling identity is proved internally. -/
theorem conditioned_probability_le_repeated_value [Nonempty O]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    conditionedWinProbability J g gamma observed reference strategy ≤
      ((incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card).value := by
  rw [conditionedWinProbability_eq_fresh J g gamma observed reference e strategy distinct,
    ← reconstructed_success_eq_fresh_average J g gamma observed reference e strategy]
  exact actual_conditioned_strategy_success_le_repeated_value
    J g gamma observed reference (incidenceLaw g) e strategy

end
end UniqueGamesTheorem.Soundness.ConditionalGameLaw

end

end OAI
