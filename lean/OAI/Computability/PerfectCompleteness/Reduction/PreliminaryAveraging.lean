import OAI.Computability.PerfectCompleteness.Sampling.PreliminarySampler

namespace OAI

section

namespace PerfectCompleteness.PreliminaryAveraging

open PreliminarySampler TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

theorem probability_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (event : X × Y → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

def directionLaw (leaf : RecursiveSpaces.Slots branch n) (level : Fin n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) := by
  letI : Nonempty (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
    directionNonempty _ (by rw [GeometricPath.nodeAtLevel_height]; exact hrows level.val)
  exact FiniteDistribution.uniform _

theorem choice_probability (leaf : RecursiveSpaces.Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) (event : Choice rows leaf → Bool) :
    (choiceLaw leaf hn hrows).probability event =
      (∑ level : Fin n, (directionLaw leaf level hrows).probability
        (fun direction => event ⟨level, direction⟩)) / (n : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change (CompletionSoundness.sigmaLaw (FiniteDistribution.uniform (Fin n))
    (fun level => directionLaw leaf level hrows)).probability event = _
  rw [CompletionSoundness.sigmaLaw_probability, FiniteDistribution.expectation_uniform]
  simp only [Fintype.card_fin]

theorem array_observation_probability [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (observe : ∀ b : Base branch n t m,
      Arrays (sourceSlots clauses (endpoints b.1)) rows → Choice rows b.2 → Bool) :
    (law clauses rows repeats hn hbranch hrows).probability
        (fun e => observe e.1
          (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
            (sourceSlots clauses (endpoints e.1.1)) e.2.1) e.2.2) =
      (baseLaw hbranch).expectation (fun b =>
        (WholeArraySampler.law rows repeats (GeometricPath.leafPath b.2)
          (sourceSlots clauses (endpoints b.1))).expectation
          (fun arrays => (choiceLaw b.2 hn hrows).probability (observe b arrays))) := by
  rw [law_probability]
  apply FiniteDistribution.expectation_congr
  intro b
  rw [conditionalLaw, probability_product]
  rw [WholeArraySampler.law, FiniteDistribution.expectation_pushforward]

theorem candidate_average [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (observe : ∀ b : Base branch n t m,
      Arrays (sourceSlots clauses (endpoints b.1)) rows → Choice rows b.2 → Bool) :
    (law clauses rows repeats hn hbranch hrows).probability
        (fun e => observe e.1
          (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
            (sourceSlots clauses (endpoints e.1.1)) e.2.1) e.2.2) =
      (baseLaw hbranch).expectation (fun b =>
        (WholeArraySampler.law rows repeats (GeometricPath.leafPath b.2)
          (sourceSlots clauses (endpoints b.1))).expectation (fun arrays =>
            (∑ level : Fin n, (directionLaw b.2 level hrows).probability
              (fun direction => observe b arrays ⟨level, direction⟩)) / (n : ℝ))) := by
  rw [array_observation_probability clauses rows repeats hn hbranch hrows observe]
  apply FiniteDistribution.expectation_congr
  intro b
  apply FiniteDistribution.expectation_congr
  intro arrays
  exact choice_probability b.2 hn hrows (observe b arrays)

end
end PerfectCompleteness.PreliminaryAveraging

end

end OAI
