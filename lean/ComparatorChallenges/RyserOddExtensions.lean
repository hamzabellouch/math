import Mathlib

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

abbrev Hypergraph (Vertex : Type*) := Finset (Finset Vertex)

variable {Vertex : Type*} [DecidableEq Vertex]

def IsCover (hypergraph : Hypergraph Vertex) (cover : Finset Vertex) : Prop :=
  ∀ edge ∈ hypergraph, ∃ vertex ∈ cover, vertex ∈ edge

def Intersecting (hypergraph : Hypergraph Vertex) : Prop :=
  ∀ edge ∈ hypergraph, ∀ other ∈ hypergraph, edge ≠ other → (edge ∩ other).Nonempty

attribute [-instance] instDecidablePairwiseCoeFinsetOfDecidableEqOfDecidableRel in
def matchings (hypergraph : Hypergraph Vertex) : Finset (Hypergraph Vertex) := by
  classical
  exact hypergraph.powerset.filter fun matching =>
    (matching : Set (Finset Vertex)).Pairwise Disjoint

def matchingNumber (hypergraph : Hypergraph Vertex) : ℕ :=
  (matchings hypergraph).sup Finset.card

def coverCardinalities (hypergraph : Hypergraph Vertex) : Set ℕ :=
  {size | ∃ cover : Finset Vertex, IsCover hypergraph cover ∧ cover.card = size}

def coverNumber (hypergraph : Hypergraph Vertex) : ℕ := sInf (coverCardinalities hypergraph)

def Uniform (rank : ℕ) (hypergraph : Hypergraph Vertex) : Prop :=
  ∀ edge ∈ hypergraph, edge.card = rank

def PartiteUniform {Index : Type*} (part : Vertex → Index)
    (hypergraph : Hypergraph Vertex) : Prop :=
  ∀ edge ∈ hypergraph, ∀ index : Index,
    ∃! vertex : Vertex, vertex ∈ edge ∧ part vertex = index

def RPartiteUniform (rank : ℕ) (hypergraph : Hypergraph Vertex) : Prop :=
  ∃ part : Vertex → Fin rank, PartiteUniform part hypergraph

end RyserCoveringCounterexample

namespace RyserOdd

open RyserCoveringCounterexample

def Specification.ExplicitFailureAt (rank : ℕ) : Prop :=
  ∃ (Vertex : Type) (finiteVertices : Fintype Vertex) (decidableVertices : DecidableEq Vertex),
    letI : Fintype Vertex := finiteVertices
    letI : DecidableEq Vertex := decidableVertices
    ∃ hypergraph : RyserCoveringCounterexample.Hypergraph Vertex,
      0 < rank ∧ hypergraph.Nonempty ∧ RPartiteUniform rank hypergraph ∧
        Uniform rank hypergraph ∧ Intersecting hypergraph ∧
        (∃ cover : Finset Vertex, IsCover hypergraph cover) ∧
        matchingNumber hypergraph = 1 ∧ coverNumber hypergraph = rank ∧
        (rank - 1) * matchingNumber hypergraph < coverNumber hypergraph

theorem eventualOddFailures_and_infinite :
    (∃ primeThreshold : ℕ, ∀ prime : ℕ, primeThreshold ≤ prime →
      prime.Prime → prime % 3 = 2 →
      ∃ degreeThreshold : ℕ, 3 ≤ degreeThreshold ∧
        ∀ degree : ℕ, degreeThreshold ≤ degree → Odd degree →
          Specification.ExplicitFailureAt (prime ^ degree + 1)) ∧
    Set.Infinite {rank : ℕ | Specification.ExplicitFailureAt rank} := by
  sorry

end RyserOdd

end

end OAI
