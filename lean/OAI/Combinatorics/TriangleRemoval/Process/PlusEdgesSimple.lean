import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Embeddings.EmptyRootInjection
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma plusEdges_simple {a b : Fin N} (hab : a ≠ b) :
    ∀ e ∈ insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ), e.card = 2 := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact Finset.card_pair hab
  · obtain ⟨v,_,u,hu,rfl⟩ := B.backEdges_mem_pair he
    exact Finset.card_pair (ne_of_lt (B.older_lt v u hu))

lemma extra_not_mem_backEdges {a b : Fin N} (hne : ¬ B.graph.Adj a b) :
    ({a,b} : Finset (Fin N)) ∉ B.backEdges Finset.univ := by
  intro he
  obtain ⟨v,_,u,hu,he⟩ := B.backEdges_mem_pair he
  have ha : a = u ∨ a = v := by
    have hm : a ∈ ({u,v} : Finset (Fin N)) := he ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hb : b = u ∨ b = v := by
    have hm : b ∈ ({u,v} : Finset (Fin N)) := he ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hc := congrArg Finset.card he
  have hab : a ≠ b := by
    intro hh
    rw [hh,Finset.pair_eq_singleton,Finset.card_singleton,
      Finset.card_pair (ne_of_lt (B.older_lt v u hu))] at hc
    omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab rfl
  · exact hne (Or.inl hu)
  · exact hne (Or.inr hu)
  · exact hab rfl

theorem short_witness_count {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) {a b : Fin N} (hab : a ≠ b)
    (hne : ¬ B.graph.Adj a b) (hcap : N ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n) :
    ((graphEmbeddingSet (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((n : ℝ)^N *
        prefixDensity n ^ ((B.backEdges Finset.univ).card + 1)) := by
  have h := graphEmbeddingSet_large_count hGood _ (B.plusEdges_simple hab) hcap
    (fun U => B.induced_plus_one_sparse U a b) hp hp1 hD
  rw [Finset.card_insert_of_notMem (B.extra_not_mem_backEdges hne)] at h
  exact h

end SharpTerminalLeave.BirthGraph

end

end OAI
