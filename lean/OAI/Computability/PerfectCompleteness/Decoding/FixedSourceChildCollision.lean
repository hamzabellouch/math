import OAI.Computability.PerfectCompleteness.Decoding.FixedProjectionErrorLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildMarkedLaw

namespace OAI

section

namespace PerfectCompleteness.FixedSourceChildCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {n height v m : Nat} [NeZero m]
  (path : Path (branch parameters) n (height + 1))
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)

abbrev Calls := Option (WholeCutCalls.Index (rows parameters.plan) (repeats parameters.plan) path)

abbrev Questions := SourceChildMarkedLaw.Questions
  (branch := branch parameters) (n := height)
  (t := sourceLength parameters.plan hδ) (m := m)

abbrev Native (q : Questions (m := m) parameters (height := height)) :=
  CutChildGrouping.Raw (C := Calls parameters path)
    (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan)

abbrev Form (q : Questions (m := m) parameters (height := height)) :=
  ChildBilinearCollisionTransfer.ParentForm (SourceChildMarkedLaw.questionSlots clauses q)

abbrev Sample := SourceChildKernel.Sample (C := Calls parameters path)
  (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated

def markedLaw : FiniteDistribution (Sample parameters path clauses designated) :=
  SourceChildKernel.originalLaw (C := Calls parameters path)
    (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated
    (fun _ => ProjectionPosterior.bernoulli (projectionProbability parameters height : ℝ)
      (by exact_mod_cast (projectionProbability_bounds parameters height).1.le)
      (by exact_mod_cast (projectionProbability_bounds parameters height).2.le))

def uniformLaw : FiniteDistribution
    (Σ q : Questions (m := m) parameters (height := height), Native parameters path clauses q) :=
  CompletionSoundness.sigmaLaw
    (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
      (t := sourceLength parameters.plan hδ) (m := m))
    (fun q => CutChildGrouping.rawLaw (C := Calls parameters path)
      (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan))

variable (F₀ F₁ : (q : Questions (m := m) parameters (height := height)) →
  Native parameters path clauses q → Option (Form parameters clauses q))

def restrictedEvent (sample : Sample parameters path clauses designated) : Bool :=
  let record := SourceChildMarkedLaw.observe (rows parameters.plan) clauses designated sample
  BilinearCollisionTransfer.restrictedCollision
    (F₀ record.1 record.2.2) (F₁ record.1 record.2.2)
    (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses record.1) record.2.1)

def fullEvent (record :
    Σ q : Questions (m := m) parameters (height := height), Native parameters path clauses q) : Bool :=
  BilinearCollisionTransfer.fullCollision (F₀ record.1 record.2) (F₁ record.1 record.2)

private theorem expectation_add_const {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) (f : A → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x + c) = μ.expectation f + c := by
  simp only [FiniteDistribution.expectation, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, μ.normalized, one_mul]

theorem restricted_probability_le (hn : n ≤ parameters.plan.depth) :
    (markedLaw parameters path clauses designated).probability
        (restrictedEvent parameters path clauses designated F₀ F₁) ≤
      (uniformLaw parameters path clauses).probability
        (fullEvent parameters path clauses F₀ F₁) + 2 * parameters.accuracy := by
  have hβ : 0 ≤ (projectionProbability parameters height : ℝ) := by
    exact_mod_cast (projectionProbability_bounds parameters height).1.le
  have hβ' : (projectionProbability parameters height : ℝ) ≤ 1 := by
    exact_mod_cast (projectionProbability_bounds parameters height).2.le
  have hlaw := SourceChildMarkedLaw.original_extended_marked_law
    (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated
    (repeats parameters.plan) path (projectionProbability parameters height : ℝ) hβ hβ'
  have hprob := congrArg
    (fun μ : FiniteDistribution
      (SourceChildMarkedLaw.Observation (C := Calls parameters path)
        (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses) =>
      μ.probability (fun record => BilinearCollisionTransfer.restrictedCollision
        (F₀ record.1 record.2.2) (F₁ record.1 record.2.2)
        (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses record.1)
          record.2.1))) hlaw
  rw [FiniteDistribution.probability_pushforward,
    CompletionSoundness.sigmaLaw_probability] at hprob
  rw [show (markedLaw parameters path clauses designated).probability
      (restrictedEvent parameters path clauses designated F₀ F₁) = _ from hprob]
  rw [uniformLaw, CompletionSoundness.sigmaLaw_probability]
  have hpoint := fun q : Questions (m := m) parameters (height := height) =>
    (FixedChildCollisionTransfer.marked_restricted_lt_uniform_full parameters
      (FixedChildCollisionTransfer.lower_pair_calls_le parameters path hn)
      (SourceChildMarkedLaw.questionSlots clauses q)
      (SourceChildMarkedLaw.projectedSlots clauses designated q)
      (SourceChildMarkedLaw.questionProjection clauses designated q)
      (fun _ => FiniteDistribution.uniform
        (SourceChildMarkedLaw.Choice (branch := branch parameters) (n := height)
          (t := sourceLength parameters.plan hδ)))
      (F₀ q) (F₁ q)).le
  have havg := SmallBias.expectation_mono
    (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
      (t := sourceLength parameters.plan hδ) (m := m)) hpoint
  rw [expectation_add_const] at havg
  simpa only [← SourceChildMarkedLaw.replacementLaws_eq, fullEvent] using havg

end
end PerfectCompleteness.FixedSourceChildCollision

end

end OAI
