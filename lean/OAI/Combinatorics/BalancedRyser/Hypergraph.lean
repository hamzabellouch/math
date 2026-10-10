import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Nat.Prime.Defs
import OAI.Combinatorics.BalancedRyser.Model

namespace OAI

namespace Balanced
open scoped _root_.Balanced

namespace PartiteHypergraph

variable {r n : ℕ}

def part (i : Fin r) : Finset (Vertex r n) :=
  Finset.univ.image (fun v : Fin n => (i, v))

def edgeVertices (e : Fin r → Fin n) : Finset (Vertex r n) :=
  Finset.univ.image (fun i : Fin r => (i, e i))

def toHypergraph (H : PartiteHypergraph r n) : Hypergraph (Vertex r n) where
  vertexSet := Set.univ
  edgeSet := {E | ∃ e ∈ H.edges, E = ↑(edgeVertices e)}
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _

def IsMatching (H : PartiteHypergraph r n) (M : Finset (Fin r → Fin n)) : Prop :=
  M ⊆ H.edges ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (edgeVertices e) (edgeVertices f)

end PartiteHypergraph

end Balanced

end OAI
