import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ReindexSetImage
import OAI.Combinatorics.TriangleRemoval.Process.SparseScalingOne
import OAI.Combinatorics.TriangleRemoval.Process.SuffixBoundary
import OAI.Combinatorics.TriangleRemoval.Process.Within
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph

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

def suffixTemplate (Z : Finset (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) : RootedTemplate (B.suffixVertices Z a b).card :=
  reindexTemplate (B.suffixVertices Z a b) (B.suffixEdges Z a b) (B.suffixBoundary Z a b)
    B.suffixEdges_subset_vertices (B.suffixEdges_simple hab) (B.suffixBoundary_independent hmark)

lemma suffixTemplate_free_card (Z : Finset (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) :
    (B.suffixVertices Z a b).card - (B.suffixTemplate Z a b hab hmark).roots.card = Z.card :=
  reindexTemplate_free_card Z _ _ _ _ _ (B.suffixBoundary_disjoint Z a b).symm

lemma suffixTemplate_edges_card {Z : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) (hborn : ∀ v ∈ Z, (B.older v).card = 2)
    (hne : ¬ B.graph.Adj a b) :
    (B.suffixTemplate Z a b hab hmark).edges.card = 2 * Z.card + 1 := by
  rw [suffixTemplate,reindexTemplate_edges_card]
  exact B.suffix_edges_card hborn hne

theorem suffixTemplate_eligible {Z : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) (hborn : ∀ v ∈ Z, (B.older v).card = 2)
    (hne : ¬ B.graph.Adj a b) (hc : B.Covered Z a b)
    (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 1 ≤ (n : ℝ) * p ^ 2)
    (hsmall : (n : ℝ) ^ Z.card * p ^ (2 * Z.card + 1) ≤ 1) :
    smallTemplateEligible (B.suffixTemplate Z a b hab hmark) n p := by
  apply smallTemplateEligible_of_sparse _ p hp hp1 hD
  · rw [B.suffixTemplate_free_card,B.suffixTemplate_edges_card hab hmark hborn hne]
    exact hsmall
  · apply reindexTemplate_sparse_transfer Z (B.suffixBoundary Z a b)
      (B.suffixEdges Z a b) _ _ _ (B.suffixBoundary_disjoint Z a b).symm
    intro U hU hproper
    exact B.proper_suffix_sparse (B.suffixBoundary_disjoint Z a b) hU hproper hborn hc

theorem suffixTemplate_count {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) {Z : Finset (Fin N)} {a b : Fin N}
    (hab : a ≠ b) (hmark : a ∈ Z ∨ b ∈ Z)
    (hborn : ∀ v ∈ Z, (B.older v).card = 2) (hne : ¬ B.graph.Adj a b)
    (hc : B.Covered Z a b) (hcap : 3 * Z.card + 1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hsmall : (n : ℝ) ^ Z.card * prefixDensity n ^ (2 * Z.card + 1) ≤ 1)
    (ψ : {v // v ∈ (B.suffixTemplate Z a b hab hmark).roots} ↪ Fin n) :
    rootedCount (B.suffixTemplate Z a b hab hmark) ψ G ≤ prefixTemplateFactor n C := by
  have horder := (B.suffixVertices_card hmark).trans hcap
  have ht := (hGood.2.2.2.2.2 _ horder (B.suffixTemplate Z a b hab hmark) ψ).2
  exact ht (B.suffixTemplate_eligible hab hmark hborn hne hc n (prefixDensity n) hp hp1 hD hsmall)

end SharpTerminalLeave.BirthGraph

end

end OAI
