import OAI.Computability.PerfectCompleteness.Foundations.PrefixTests
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryLevelPair
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.CanonicalDirections

open RecursiveSpaces HierarchicalArrays PreliminarySampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n : Nat}

abbrev Tuple (rows : Nat → Nat) (n : Nat) :=
  (level : Fin n) → PrefixTests.LevelDirection rows level

def directionEquiv (rows : Nat → Nat) (leaf : Slots branch n) (level : Fin n) :
    PrefixTests.LevelDirection rows level ≃
      BucketSampler.Direction (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level))) :=
  (Equiv.cast (congrArg (fun height => BucketSampler.Direction (rows height))
    (GeometricPath.nodeAtLevel_height leaf level))).symm

def tupleEquiv (rows : Nat → Nat) (leaf : Slots branch n) :
    Tuple rows n ≃ CandidateCoupling.DirectionTuple rows leaf :=
  Equiv.piCongrRight (directionEquiv rows leaf)

@[simp] theorem tupleEquiv_apply (rows : Nat → Nat) (leaf : Slots branch n)
    (directions : Tuple rows n) (level : Fin n) :
    tupleEquiv rows leaf directions level = directionEquiv rows leaf level (directions level) := rfl

@[simp] theorem tupleEquiv_symm_apply (rows : Nat → Nat) (leaf : Slots branch n)
    (directions : CandidateCoupling.DirectionTuple rows leaf) (level : Fin n) :
    (tupleEquiv rows leaf).symm directions level =
      (directionEquiv rows leaf level).symm (directions level) := rfl

def levelLaw (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) (level : Fin n) :
    FiniteDistribution (PrefixTests.LevelDirection rows level) := by
  letI := directionNonempty (rows (level.val + 1)) (hrows level.val)
  exact FiniteDistribution.uniform _

def law (rows : Nat → Nat) (n : Nat) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Tuple rows n) :=
  FiniteProduct.law (levelLaw rows hrows)

theorem directionLaw_toCanonical (rows : Nat → Nat) (leaf : Slots branch n)
    (level : Fin n) (hrows : ∀ k, 0 < rows (k + 1)) :
    (PreliminaryAveraging.directionLaw leaf level hrows).pushforward
        (directionEquiv rows leaf level).symm = levelLaw rows hrows level := by
  let : Nonempty (PrefixTests.LevelDirection rows level) :=
    directionNonempty (rows (level.val + 1)) (hrows level.val)
  let : Nonempty (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
    directionNonempty _ (by rw [GeometricPath.nodeAtLevel_height]; exact hrows level.val)
  change (FiniteDistribution.uniform
      (BucketSampler.Direction (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level))))).pushforward
      (directionEquiv rows leaf level).symm =
    FiniteDistribution.uniform (PrefixTests.LevelDirection rows level)
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (directionEquiv rows leaf level).symm

theorem directionsLaw_toCanonical (rows : Nat → Nat) (leaf : Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    (CandidateCoupling.directionsLaw leaf hrows).pushforward (tupleEquiv rows leaf).symm =
      law rows n hrows := by
  change (FiniteProduct.law (fun level => PreliminaryAveraging.directionLaw leaf level hrows)).pushforward
    (fun directions level => (directionEquiv rows leaf level).symm (directions level)) = _
  rw [FiniteProduct.pushforward_map]
  apply congrArg (fun laws : (level : Fin n) →
    FiniteDistribution (PrefixTests.LevelDirection rows level) => FiniteProduct.law laws)
  funext level
  exact directionLaw_toCanonical rows leaf level hrows

theorem canonicalLaw_toDirections (rows : Nat → Nat) (leaf : Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    (law rows n hrows).pushforward (tupleEquiv rows leaf) =
      CandidateCoupling.directionsLaw leaf hrows := by
  have h := congrArg
    (fun μ : FiniteDistribution (Tuple rows n) => μ.pushforward (tupleEquiv rows leaf))
    (directionsLaw_toCanonical rows leaf hrows)
  rw [FiniteDistribution.pushforward_comp] at h
  have hid : (fun directions : CandidateCoupling.DirectionTuple rows leaf =>
      tupleEquiv rows leaf ((tupleEquiv rows leaf).symm directions)) = id := by
    funext directions
    exact (tupleEquiv rows leaf).apply_symm_apply directions
  rw [hid, FiniteDistribution.pushforward_id] at h
  exact h.symm

@[simp] theorem choiceAt_toCanonical (rows : Nat → Nat) (leaf : Slots branch n)
    (directions : CandidateCoupling.DirectionTuple rows leaf) (level : Fin n) :
    PrefixTests.choiceAt rows leaf level ((tupleEquiv rows leaf).symm directions level) =
      (⟨level, directions level⟩ : Choice rows leaf) := by
  change (⟨level, directionEquiv rows leaf level
    ((directionEquiv rows leaf level).symm (directions level))⟩ : Choice rows leaf) = _
  rw [Equiv.apply_symm_apply]

variable {v m t : Nat} {rows repeats : Nat → Nat}

theorem win_eq_observe_canonical (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (b : Base branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (endpoints b.1)) rows)
    (directions : Tuple rows n) (level : Fin n) :
    PreliminaryLevelPair.win clauses strategy level
        ⟨b, arrays, tupleEquiv rows b.2 directions⟩ =
      PreliminaryStrategy.observe clauses
        (PreliminaryStrategy.extend clauses branch n t rows repeats strategy) b arrays
        (PrefixTests.choiceAt rows b.2 level (directions level)) := rfl

theorem win_eq_observe (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (level : Fin n) (e : CandidateCoupling.Shared clauses branch n t rows) :
    PreliminaryLevelPair.win clauses strategy level e =
      PreliminaryStrategy.observe clauses
        (PreliminaryStrategy.extend clauses branch n t rows repeats strategy) e.1 e.2.1
        (PrefixTests.choiceAt rows e.1.2 level
          ((tupleEquiv rows e.1.2).symm e.2.2 level)) := by
  rw [choiceAt_toCanonical]
  rfl

end
end PerfectCompleteness.CanonicalDirections

end

end OAI
