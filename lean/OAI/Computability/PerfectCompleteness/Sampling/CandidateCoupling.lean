import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryAveraging

namespace OAI


namespace PerfectCompleteness.CandidateCoupling

open PreliminarySampler PreliminaryAveraging TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

section Selection

variable {I : Type*} [Fintype I] [DecidableEq I]
  {D : I → Type*} [∀ i, Fintype (D i)]

theorem selected_probability (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (D i)) (event : (Σ i, D i) → Bool) :
    (μ.product (FiniteProduct.law ν)).probability
        (fun z => event ⟨z.1, z.2 z.1⟩) =
      (CompletionSoundness.sigmaLaw μ ν).probability event := by
  rw [probability_product, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro i
  have h := FiniteDistribution.probability_pushforward
    (FiniteProduct.law ν) (fun directions => directions i)
    (fun direction => event ⟨i, direction⟩)
  rw [FiniteProduct.eval_pushforward] at h
  exact h.symm

theorem selected_pushforward (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (D i)) :
    (μ.product (FiniteProduct.law ν)).pushforward
        (fun z => (⟨z.1, z.2 z.1⟩ : Σ i, D i)) =
      CompletionSoundness.sigmaLaw μ ν := by
  apply FiniteDistribution.eq_of_weight_eq
  intro choice
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.probability_pushforward]
  exact selected_probability μ ν (fun c => decide (c = choice))

omit [DecidableEq I] in
theorem expectation_sigmaLaw (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (D i)) (f : (Σ i, D i) → ℝ) :
    (CompletionSoundness.sigmaLaw μ ν).expectation f =
      μ.expectation (fun i => (ν i).expectation (fun d => f ⟨i, d⟩)) := by
  simp only [FiniteDistribution.expectation, CompletionSoundness.sigmaLaw,
    Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

end Selection

theorem probability_eq_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

theorem expectation_div {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (f : X → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x / c) = μ.expectation f / c := by
  simp only [FiniteDistribution.expectation, mul_div_assoc, Finset.sum_div]

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

abbrev DirectionTuple (rows : Nat → Nat) (leaf : RecursiveSpaces.Slots branch n) :=
  (level : Fin n) → BucketSampler.Direction
    (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))

def directionsLaw (leaf : RecursiveSpaces.Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1)) : FiniteDistribution (DirectionTuple rows leaf) :=
  FiniteProduct.law (fun level => directionLaw leaf level hrows)

theorem directions_marginal (leaf : RecursiveSpaces.Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1)) (level : Fin n) :
    (directionsLaw leaf hrows).pushforward (fun directions => directions level) =
      directionLaw leaf level hrows :=
  FiniteProduct.eval_pushforward _ level

theorem directions_expectation_product (leaf : RecursiveSpaces.Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1))
    (f : (level : Fin n) → BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level))) → ℝ) :
    (directionsLaw leaf hrows).expectation (fun directions => ∏ level, f level (directions level)) =
      ∏ level, (directionLaw leaf level hrows).expectation (f level) :=
  FiniteProduct.expectation_product _ f

def selectedTupleLaw (leaf : RecursiveSpaces.Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Fin n × DirectionTuple rows leaf) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (FiniteDistribution.uniform (Fin n)).product (directionsLaw leaf hrows)

theorem selectedTupleLaw_pushforward (leaf : RecursiveSpaces.Slots branch n)
    (hn : 0 < n) (hrows : ∀ k, 0 < rows (k + 1)) :
    (selectedTupleLaw leaf hn hrows).pushforward
        (fun z => (⟨z.1, z.2 z.1⟩ : Choice rows leaf)) = choiceLaw leaf hn hrows := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact selected_pushforward (FiniteDistribution.uniform (Fin n))
    (fun level => directionLaw leaf level hrows)

def candidateFraction (leaf : RecursiveSpaces.Slots branch n)
    (event : Choice rows leaf → Bool) (directions : DirectionTuple rows leaf) : ℝ :=
  (∑ level : Fin n, if event ⟨level, directions level⟩ then 1 else 0) / (n : ℝ)

theorem choice_probability_candidateFraction (leaf : RecursiveSpaces.Slots branch n)
    (hn : 0 < n) (hrows : ∀ k, 0 < rows (k + 1))
    (event : Choice rows leaf → Bool) :
    (choiceLaw leaf hn hrows).probability event =
      (directionsLaw leaf hrows).expectation (candidateFraction leaf event) := by
  rw [choice_probability]
  change (∑ level : Fin n, (directionLaw leaf level hrows).probability
      (fun direction => event ⟨level, direction⟩)) / (n : ℝ) =
    (directionsLaw leaf hrows).expectation
      (fun directions => (∑ level : Fin n,
        if event ⟨level, directions level⟩ then 1 else 0) / (n : ℝ))
  rw [expectation_div, SmallBias.expectation_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro level _
  rw [probability_eq_expectation]
  exact (FiniteProduct.expectation_eval
    (fun level => directionLaw leaf level hrows) level
    (fun direction => if event ⟨level, direction⟩ then (1 : ℝ) else 0)).symm

abbrev Shared (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :=
  (b : Base branch n t m) ×
    (Arrays (sourceSlots clauses (endpoints b.1)) rows × DirectionTuple rows b.2)

def conditionalSharedLaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1))
    (b : Base branch n t m) :
    FiniteDistribution
      (Arrays (sourceSlots clauses (endpoints b.1)) rows × DirectionTuple rows b.2) :=
  (WholeArraySampler.law rows repeats (GeometricPath.leafPath b.2)
    (sourceSlots clauses (endpoints b.1))).product (directionsLaw b.2 hrows)

def sharedLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Shared clauses branch n t rows) :=
  CompletionSoundness.sigmaLaw (baseLaw hbranch)
    (conditionalSharedLaw clauses rows repeats hrows)

theorem candidate_average_shared [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (observe : ∀ b : Base branch n t m,
      Arrays (sourceSlots clauses (endpoints b.1)) rows → Choice rows b.2 → Bool) :
    (PreliminarySampler.law clauses rows repeats hn hbranch hrows).probability
        (fun e => observe e.1
          (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
            (sourceSlots clauses (endpoints e.1.1)) e.2.1) e.2.2) =
      (sharedLaw clauses rows repeats hbranch hrows).expectation
        (fun e => candidateFraction e.1.2 (observe e.1 e.2.1) e.2.2) := by
  rw [array_observation_probability clauses rows repeats hn hbranch hrows observe,
    sharedLaw, expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro b
  rw [conditionalSharedLaw, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro arrays
  exact choice_probability_candidateFraction b.2 hn hrows (observe b arrays)

end
end PerfectCompleteness.CandidateCoupling

end OAI
