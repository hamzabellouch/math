import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI


namespace PerfectCompleteness.UniformLatent

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

theorem probability_uniform_singleton {A : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] (a : A) :
    (FiniteDistribution.uniform A).probability (fun x => decide (x = a)) =
      1 / (Fintype.card A : ℝ) := by
  simp [FiniteDistribution.probability, FiniteDistribution.uniform]


variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq J]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

abbrev Raw := Σ s : S, (j : J) → Ω s j

def latentKernel (s : S) : FiniteDistribution (Raw Ω) :=
  (law (fun j => FiniteDistribution.uniform (Ω s j))).pushforward
    (fun x => (⟨s, x⟩ : Raw Ω))

variable [∀ s j, DecidableEq (Ω s j)]

def zeroEvent (zero : (s : S) → (j : J) → Ω s j) (x : Raw Ω) : Bool :=
  decide (∀ j, x.2 j = zero x.1 j)

theorem probability_latentKernel_zero (zero : (s : S) → (j : J) → Ω s j) (s : S) :
    (latentKernel Ω s).probability (zeroEvent Ω zero) =
      ∏ j, 1 / (Fintype.card (Ω s j) : ℝ) := by
  rw [latentKernel, FiniteDistribution.probability_pushforward]
  have hevent : (fun x => zeroEvent Ω zero (⟨s, x⟩ : Raw Ω)) =
      allEvent (fun j a => decide (a = zero s j)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [zeroEvent, allEvent]
  rw [hevent, probability_law_all]
  apply Finset.prod_congr rfl
  intro j _
  exact probability_uniform_singleton (zero s j)

theorem probability_latentKernel_zero_pos (zero : (s : S) → (j : J) → Ω s j)
    (s : S) : 0 < (latentKernel Ω s).probability (zeroEvent Ω zero) := by
  rw [probability_latentKernel_zero]
  apply Finset.prod_pos
  intro j _
  exact one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

theorem probability_latentKernel_zero_constant
    (zero : (s : S) → (j : J) → Ω s j) (cardinality : J → Nat)
    (same_cardinality : ∀ s j, Fintype.card (Ω s j) = cardinality j) (s : S) :
    (latentKernel Ω s).probability (zeroEvent Ω zero) =
      ∏ j, 1 / (cardinality j : ℝ) := by
  rw [probability_latentKernel_zero]
  simp only [same_cardinality]


variable {D : Type*} [Fintype D]

def projectedKernel (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) :
    FiniteDistribution (Sum D (Raw Ω)) :=
  flag.mixture (fun b => if b then
    (latentKernel Ω s).pushforward Sum.inr else (nonprojected s).pushforward Sum.inl)

def projectedZero (zero : (s : S) → (j : J) → Ω s j) : Sum D (Raw Ω) → Bool
  | Sum.inl _ => false
  | Sum.inr x => zeroEvent Ω zero x

theorem probability_projectedKernel_zero (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D)
    (zero : (s : S) → (j : J) → Ω s j) (s : S) :
    (projectedKernel Ω flag nonprojected s).probability (projectedZero Ω zero) =
      flag.weight true * (∏ j, 1 / (Fintype.card (Ω s j) : ℝ)) := by
  simp [projectedKernel, FiniteDistribution.probability_mixture,
    FiniteDistribution.probability_pushforward, projectedZero,
    probability_latentKernel_zero]

theorem probability_projectedKernel_zero_constant (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D)
    (zero : (s : S) → (j : J) → Ω s j) (cardinality : J → Nat)
    (same_cardinality : ∀ s j, Fintype.card (Ω s j) = cardinality j) (s : S) :
    (projectedKernel Ω flag nonprojected s).probability (projectedZero Ω zero) =
      flag.weight true * (∏ j, 1 / (cardinality j : ℝ)) := by
  rw [probability_projectedKernel_zero]
  simp only [same_cardinality]

theorem probability_projectedKernel_zero_binary (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D)
    (zero : (s : S) → (j : J) → Ω s j) (dimension : J → Nat)
    (same_dimension : ∀ s j, Fintype.card (Ω s j) = 2 ^ dimension j) (s : S) :
    (projectedKernel Ω flag nonprojected s).probability (projectedZero Ω zero) =
      flag.weight true / (2 : ℝ) ^ (∑ j, dimension j) := by
  rw [probability_projectedKernel_zero_constant Ω flag nonprojected zero
    (fun j => 2 ^ dimension j) same_dimension]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Finset.prod_div_distrib,
    Finset.prod_const_one, Finset.prod_pow_eq_pow_sum, mul_one_div]

theorem source_condition_projected [DecidableEq S] (μ : FiniteDistribution S)
    (flag : FiniteDistribution Bool) (nonprojected : S → FiniteDistribution D)
    (zero : (s : S) → (j : J) → Ω s j) (cardinality : J → Nat)
    (same_cardinality : ∀ s j, Fintype.card (Ω s j) = cardinality j)
    (positive : 0 < (kernelJoint μ (projectedKernel Ω flag nonprojected)).probability
      (fun x => projectedZero Ω zero x.2)) :
    ((kernelJoint μ (projectedKernel Ω flag nonprojected)).condition
      (fun x => projectedZero Ω zero x.2) positive).pushforward Prod.fst = μ := by
  apply source_condition_of_constant μ _ _
    (flag.weight true * (∏ j, 1 / (cardinality j : ℝ))) _ positive
  intro s
  exact probability_projectedKernel_zero_constant Ω flag nonprojected zero
    cardinality same_cardinality s


end
end PerfectCompleteness.UniformLatent

end OAI
