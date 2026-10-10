import Mathlib
import OAI.Computability.VertexCover.Encoding.BinaryEncoding

namespace OAI

section

namespace VertexCover

def ThreeSAT (input : List Bool) : Prop :=
  ∃ formula, UniqueGames.BinaryEncoding.decodeFormula input = some formula ∧
    formula.Satisfiable

structure ExplicitGraph where
  n : ℕ
  edges : List (Fin n × Fin n)
  increasing : ∀ e ∈ edges, e.1 < e.2
  nodup : edges.Nodup

namespace ExplicitGraph

def Cover (G : ExplicitGraph) (S : Finset (Fin G.n)) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ S ∨ e.2 ∈ S

instance (G : ExplicitGraph) (S : Finset (Fin G.n)) : Decidable (G.Cover S) :=
  inferInstanceAs (Decidable (∀ e ∈ G.edges, e.1 ∈ S ∨ e.2 ∈ S))

noncomputable def coverNumber (G : ExplicitGraph) : ℕ :=
  Nat.find (show ∃ k : ℕ, ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = k from
    ⟨G.n, Finset.univ, by simp [Cover], by simp⟩)

def bits (G : ExplicitGraph) : List Bool :=
  let names := [G.n] ++ List.range G.n ++ [G.edges.length] ++
    G.edges.flatMap (fun e => [e.1.val, e.2.val])
  names.flatMap UniqueGames.BinaryEncoding.nameBits

end ExplicitGraph

def FiniteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

structure GapReduction (m : ℕ) where
  construct : List Bool → ExplicitGraph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    ExplicitGraph.bits construct
  finiteAlphabet : FiniteAlphabet computation.tm
  completeness : ∀ input, ThreeSAT input →
    ((construct input).coverNumber : ℝ) <
      (1 / 2 + 1 / (m : ℝ)) * (construct input).n
  soundness : ∀ input, ¬ ThreeSAT input →
    (1 - 1 / (m : ℝ)) * (construct input).n <
      ((construct input).coverNumber : ℝ)

def natListBits (L : List ℕ) : List Bool :=
  (L.length :: L).flatMap UniqueGames.BinaryEncoding.nameBits

structure Approximation (α : ℝ) where
  run : ExplicitGraph → List ℕ
  computation : Turing.TM2ComputableInPolyTime ExplicitGraph.bits natListBits run
  finiteAlphabet : FiniteAlphabet computation.tm
  nodup : ∀ G, (run G).Nodup
  vertices : ∀ G, ∀ v ∈ run G, v < G.n
  covers : ∀ G, ∀ e ∈ G.edges, e.1.val ∈ run G ∨ e.2.val ∈ run G
  quality : ∀ G, ((run G).length : ℝ) ≤ α * (G.coverNumber : ℝ)

structure ThreeSATDecision where
  run : List Bool → Bool
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (fun b : Bool => [b]) run
  finiteAlphabet : FiniteAlphabet computation.tm
  correct : ∀ input, run input = true ↔ ThreeSAT input

end VertexCover


end

end OAI
