import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon
import OAI.Combinatorics.TriangleRemoval.Probability.ProductPMF
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.Within
import OAI.Combinatorics.TriangleRemoval.Process.SuffixBoundary
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSet
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSetMatching
import OAI.Combinatorics.TriangleRemoval.Embeddings.RestrictLabel
import OAI.Combinatorics.TriangleRemoval.Embeddings.SuffixTemplate

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
variable {N n : ℕ} (B : BirthGraph N)

theorem long_witness_matching_count {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hsmall : (n : ℝ)^(-c) ≤ 1)
    (r k : ℕ) (hrk : 2*r ≤ k) (hk : k ≤ N)
    (u v : Fin r → Fin (2*r))
    (hcoverRoots : ∀ i : Fin (2*r), ∃ j, i = u j ∨ i = v j)
    (hroot : ∀ j, B.graph.Adj (Fin.castLE (hrk.trans hk) (u j))
      (Fin.castLE (hrk.trans hk) (v j)))
    (hborn : ∀ v : Fin N, 2*r ≤ v.val → (B.older v).card = 2)
    {a b : Fin N} (hab : a ≠ b) (hne : ¬ B.graph.Adj a b)
    (hmark : k ≤ a.val ∨ k ≤ b.val)
    (hc : B.Covered (Finset.univ.filter (fun x => k ≤ x.val)) a b)
    (hcap : 3 * (N-k) + 1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hscale : (n : ℝ)^(N-k) * prefixDensity n ^ (2*(N-k)+1) ≤ 1) :
    ((graphEmbeddingSet (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((2 * prefixM n)^r * (2 * prefixD n)^(k-2*r)) := by
  classical
  let Z : Finset (Fin N) := Finset.univ.filter (fun x => k ≤ x.val)
  have hZ : Z.card = N-k := by
    have heq : Z = Finset.univ \ (Finset.univ.filter (fun x : Fin N => x.val < k)) := by
      ext x
      simp only [Z,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and,not_lt]
    rw [heq,Finset.card_sdiff_of_subset (Finset.filter_subset _ _),Finset.card_univ,
      Fintype.card_fin,Fin.card_filter_val_lt,Nat.min_eq_right hk]
  have hm : a ∈ Z ∨ b ∈ Z := by simpa only [Z,Finset.mem_filter,Finset.mem_univ,true_and] using hmark
  have hb : ∀ v ∈ Z, (B.older v).card = 2 := by
    intro v hv
    exact hborn v (hrk.trans (Finset.mem_filter.mp hv).2)
  have hIP : B.suffixBoundary Z a b ⊆ initialVertices N k := by
    intro x hx
    have hnZ := (B.mem_suffixBoundary Z a b x).mp hx |>.2
    simp only [Z,Finset.mem_filter,Finset.mem_univ,true_and,not_le] at hnZ
    exact (mem_initialVertices N k x).mpr hnZ
  have hcover : initialVertices N k ∪ B.suffixVertices Z a b = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x.val < k
    · exact Finset.mem_union_left _ ((mem_initialVertices N k x).mpr hx)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩))
  have hEF : B.suffixEdges Z a b ⊆
      insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ) := by
    apply Finset.insert_subset_insert
    exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ Z)
  have hf := graphEmbeddingSet_count_glue (B.suffixVertices Z a b) (B.suffixBoundary Z a b)
    (initialVertices N k) (B.suffixEdges Z a b) _ G B.suffixEdges_subset_vertices
    (B.suffixEdges_simple hab) (B.suffixBoundary_independent hm) hIP hcover hEF
    (B.initialAssignmentSet G k hk) (fun φ hφ => B.initialLabel_mem G hφ k hk)
    (prefixTemplateFactor n C) (by
      intro ξ _
      exact B.suffixTemplate_count hGood hab hm hb hne hc (hZ ▸ hcap) hp hp1 hD
        (hZ ▸ hscale) _)
  have hκ : 0 ≤ prefixTemplateFactor n C := by
    unfold prefixTemplateFactor
    positivity
  exact hf.trans (mul_le_mul_of_nonneg_left
    (B.initialAssignmentSet_matching_bound hGood hsmall r k hrk hk u v hcoverRoots hroot hborn) hκ)

end SharpTerminalLeave.BirthGraph

open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

end

end OAI
