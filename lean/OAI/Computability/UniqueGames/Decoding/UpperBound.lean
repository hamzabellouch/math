import OAI.Computability.UniqueGames.Decoding.ProductLaw
import OAI.Computability.UniqueGames.Decoding.WeightedPartition
import OAI.Computability.UniqueGames.Soundness.ConditionalSimulationLemmas

namespace OAI

namespace UniqueGamesTheorem.Clean.UpperBound

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- The true weighted occurrence/position experiment at fixed visible advice. -/
def fixedAdviceSuccess (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) : ℝ :=
  (FiniteDistribution.table (fun _ : P => μ)).probability
    (fun draw => decide (actualWin J g gamma strategy draw))

omit [DecidableEq R] [Fintype N] in
private theorem reference_of_positive
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (name : O → Fin 3 → N) (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) name draw = observed))) :
    Nonempty (RawObservationFibre J name gamma observed) := by
  classical
  have exists_draw : ∃ draw : Draw P O,
      outsideRecord (zeroSet J gamma) name draw = observed := by
    by_contra h
    have absent : ∀ draw : Draw P O,
        outsideRecord (zeroSet J gamma) name draw ≠ observed := by
      simpa only [not_exists] using h
    simp [FiniteDistribution.probability, absent] at positive
  obtain ⟨draw, equality⟩ := exists_draw
  exact ⟨⟨(gamma, draw), rfl, equality⟩⟩

/-- On each positive public observation fibre, the full agreement event is
bounded by ordinary repetition. The reference draw is fixed public padding,
not an extra input depending on the still hidden question pair. -/
theorem conditioned_success_le_repeated_value_with_reference
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let event : (Fin (zeroSet J gamma).card → O × N) → Bool :=
    fun questions => decide (reconstructedEvent J g gamma observed reference e strategy questions)
  have agree : ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) =
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability
      (fun draw => event (fun i => incidence g.name (draw (e i).val))) := by
    unfold FiniteDistribution.probability FiniteDistribution.condition
    apply Finset.sum_congr rfl
    intro draw _
    by_cases hdraw : outsideRecord (zeroSet J gamma) g.name draw = observed
    · let sample : RawObservationFibre J g.name gamma observed :=
        ⟨(gamma, draw), rfl, hdraw⟩
      have equivalent : actualWin J g gamma strategy draw ↔
          reconstructedEvent J g gamma observed reference e strategy
            (fun i => incidence g.name (draw (e i).val)) :=
        actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct sample
      simp only [event, decide_eq_true_eq, equivalent]
    · simp [hdraw]
  have distribution_law :=
    ProductLaw.conditioned_incidence_reindex μ J g.name gamma observed positive e event
  apply (le_of_eq (agree.trans distribution_law)).trans
  let G := (incidenceGame g (μ.pushforward (incidence g.name))).repetition (zeroSet J gamma).card
  let simulation := actualLocalSimulation J g gamma observed reference
    (μ.pushforward (incidence g.name)) e
  let induced := Simulation.strategyPair (simulation.induced strategy)
  refine le_trans ?_ (G.success_le_value induced)
  change ((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).probability event ≤
    (((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).transport
      (Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability (G.wins induced)
  rw [FiniteDistribution.probability_transport]
  apply FiniteDistribution.probability_mono
  intro questions hwin
  have houter : strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (simulation.questionA (fun i => (questions i).1))
      (simulation.questionB (fun i => (questions i).2)) :=
    of_decide_eq_true hwin
  exact simulation.induced_wins strategy _ _ houter

theorem conditioned_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let reference := Classical.choice (reference_of_positive μ J g.name gamma observed positive)
  let e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma) :=
    (Fintype.equivFinOfCardEq (by simp [PositionInside])).symm
  exact conditioned_success_le_repeated_value_with_reference
    μ J g gamma observed positive reference e strategy distinct

/-- All outside observations are genuinely averaged with their actual weights.
The result permits arbitrary repeated occurrence IDs and correlated local
answers across the entire clean tuple. -/
theorem fixed_advice_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    fixedAdviceSuccess μ J g gamma strategy ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  unfold fixedAdviceSuccess
  apply WeightedPartition.probability_le_of_conditional_le
    _ (outsideRecord (zeroSet J gamma) g.name)
  intro observed positive
  exact conditioned_success_le_repeated_value μ J g gamma observed positive strategy distinct

end
end UniqueGamesTheorem.Clean.UpperBound

end OAI
