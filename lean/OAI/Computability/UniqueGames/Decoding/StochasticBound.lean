import OAI.Computability.UniqueGames.Decoding.NativeExperiment
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

/-!
Local randomized advice responses are bounded using complete independently
sampled response tables. The verifier questions are the actual weighted
pushforward of the occurrence/position draw, with the complete private row
input retained on each side. No response sees the opposite private question.

The outer mask and coefficient tuple may be fixed before selecting either
response kernel. Revealing these data only strengthens this upper bound; they
contain no clean question or agreement event. The quantitative game-repetition
rate is a separate input to the final averaging lemma.
-/

namespace UniqueGamesTheorem.Clean.StochasticBound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds
open scoped BigOperators

noncomputable section

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- The common weighted-game interface for the actual fixed-advice experiment. -/
def actualGame (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) :
    Game (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P) :=
  Simulation.weightedGame (ActualProjection.predicateGame (R := R) g (membershipBool J))
    ((FiniteDistribution.table (fun _ : P => μ)).pushforward fun draw =>
      (actualFirst J gamma draw, actualSecond J g.name gamma draw))

abbrev fixedAdviceGame := @actualGame

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in
/-- The two deterministic strategy representations have exactly the same
winning probability under the explicitly constructed question law. -/
theorem success_eq_fixedAdviceSuccess
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : Strategy (ZeroInformation.FirstInput P R O)
      (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (actualGame μ J g gamma).success strategy =
      UpperBound.fixedAdviceSuccess μ J g gamma ⟨strategy.1, strategy.2⟩ := by
  classical
  unfold Game.success actualGame Simulation.weightedGame UpperBound.fixedAdviceSuccess
  rw [FiniteDistribution.probability_pushforward]
  rfl

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in
/-- Each stochastic local response has a deterministic complete response table
with at least its success probability. The table is chosen before the questions. -/
theorem exists_deterministic_ge_stochastic
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (responses₁ : ZeroInformation.FirstInput P R O →
      FiniteDistribution (ActualProjection.FirstAnswer P))
    (responses₂ : ZeroInformation.SecondInput P R O N →
      FiniteDistribution (ActualProjection.SecondAnswer P)) :
    ∃ strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N),
      (actualGame μ J g gamma).stochasticSuccess responses₁ responses₂ ≤
        UpperBound.fixedAdviceSuccess μ J g gamma strategy := by
  classical
  obtain ⟨strategy, h⟩ :=
    (actualGame μ J g gamma).exists_deterministic_ge_stochastic responses₁ responses₂
  refine ⟨⟨strategy.1, strategy.2⟩, ?_⟩
  calc
    _ ≤ (actualGame μ J g gamma).success strategy := h
    _ = _ := success_eq_fixedAdviceSuccess μ J g gamma strategy

theorem fixed_advice_stochastic_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (responses₁ : ZeroInformation.FirstInput P R O →
      FiniteDistribution (ActualProjection.FirstAnswer P))
    (responses₂ : ZeroInformation.SecondInput P R O N →
      FiniteDistribution (ActualProjection.SecondAnswer P))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (actualGame μ J g gamma).stochasticSuccess responses₁ responses₂ ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  obtain ⟨strategy, h⟩ := exists_deterministic_ge_stochastic μ J g gamma responses₁ responses₂
  exact h.trans (UpperBound.fixed_advice_success_le_repeated_value μ J g gamma strategy distinct)

/-- A pair of response kernels, each indexed only by its own complete input. -/
abbrev Responses (P R O N : Type) [Fintype P] [DecidableEq P] :=
  (ZeroInformation.FirstInput P R O → FiniteDistribution (ActualProjection.FirstAnswer P)) ×
  (ZeroInformation.SecondInput P R O N → FiniteDistribution (ActualProjection.SecondAnswer P))

/-- The native experiment samples a mask, then the actual coefficient tuple.
The kernels may depend on these public choices but not on an opposite input. -/
def nativeStochasticSuccess (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      (RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R))).expectation
      fun gamma => (actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (responses mask gamma).1 (responses mask gamma).2

private theorem expectation_mono {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

omit [DecidableEq O] [DecidableEq N] in
/-- The deterministic witness family is indexed by the pre-question public
data only. No single global deterministic strategy is claimed here. -/
theorem native_stochastic_le_deterministic
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) :
    ∃ strategy : NativeExperiment.MaskStrategy k R O N,
      nativeStochasticSuccess k μ g β hβ₀ hβ₁ responses ≤
        NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  classical
  let strategy : NativeExperiment.MaskStrategy k R O N := fun mask gamma =>
    Classical.choose (exists_deterministic_ge_stochastic μ (NativeExperiment.maskSet mask)
      g gamma (responses mask gamma).1 (responses mask gamma).2)
  refine ⟨strategy, ?_⟩
  unfold nativeStochasticSuccess NativeExperiment.success
  apply expectation_mono
  intro mask
  apply expectation_mono
  intro gamma
  exact Classical.choose_spec (exists_deterministic_ge_stochastic μ
    (NativeExperiment.maskSet mask) g gamma (responses mask gamma).1 (responses mask gamma).2)

/-- Stochastic kernels satisfy the same exact clean-mask moment as deterministic
ones. The only supplied rate is for the actual ordinary repeated incidence game. -/
theorem native_stochastic_le_mask_moment
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) (ρ : ℝ)
    (rate : ∀ n, ((incidenceGame g (μ.pushforward (incidence g.name))).repetition n).value ≤ ρ ^ n) :
    nativeStochasticSuccess k μ g β hβ₀ hβ₁ responses ≤
      (1 - cleanProbability β (ZeroInformation.Bits R) * (1 - ρ)) ^ k := by
  obtain ⟨strategy, h⟩ := native_stochastic_le_deterministic k μ g β hβ₀ hβ₁ responses
  rw [NativeExperiment.success_eq_flat] at h
  exact h.trans (Experiment.success_le_of_repetition k μ g
    (FiniteDistribution.uniform (Experiment.Additional k R)) β hβ₀ hβ₁
    (NativeExperiment.liftStrategy strategy) distinct ρ rate)

end
end UniqueGamesTheorem.Clean.StochasticBound

end

end OAI
