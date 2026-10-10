import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Embeddings.RestrictLabel
import OAI.Combinatorics.TriangleRemoval.Embeddings.SuffixTemplate
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSet
import OAI.Combinatorics.TriangleRemoval.Process.RootClosers
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddingsAfterRoots
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraphDegree

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N n : ℕ} (B : BirthGraph N)

theorem initialAssignmentSet_bound_unordered {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hsmall : (n : ℝ)^(-c) ≤ 1)
    (hp : 0 ≤ prefixDensity n) (r k : ℕ) (hrk : 2*r ≤ k) (hk : k ≤ N)
    (hroot : (B.rootClosers (2*r)).card = r)
    (hborn : ∀ v : Fin N, 2*r ≤ v.val → (B.older v).card = 2) :
    ((B.initialAssignmentSet G k hk).card : ℝ) ≤
      (4 * prefixM n)^r * (2 * prefixD n)^(k-2*r) := by
  classical
  have hD0 : 0 ≤ 2 * prefixD n := by unfold prefixD; positivity
  have hΔ0 : 0 ≤ 2 * (n : ℝ) * prefixDensity n := by positivity
  have hgrow := prefixEmbeddings_after_roots B.graph (lookupGraph G) (2*r) k hrk hk
    (2 * prefixD n) hD0 (goodPrefix_codegree_bound hGood hsmall)
    (fun i hi hN => B.two_preceding_neighbors (2*r) hborn i hi hN)
  have hroots := B.prefixEmbeddings_unordered_roots (lookupGraph G) (2*r) (hrk.trans hk)
    (2 * ((n : ℝ) * prefixDensity n)) (by nlinarith)
    (goodPrefix_degree_bound hGood hsmall hp)
  have hid : (n : ℝ) * (2 * ((n : ℝ) * prefixDensity n)) = 4 * prefixM n := by
    unfold prefixM
    ring
  have hrsub : 2*r-r = r := by omega
  simp only [Fintype.card_fin,hroot,hrsub] at hroots
  rw [← mul_pow,hid] at hroots
  exact (Nat.cast_le.mpr (B.initialAssignmentSet_card G k hk)).trans
    (hgrow.trans (mul_le_mul_of_nonneg_right hroots (pow_nonneg hD0 _)))

theorem long_witness_count_unordered {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hsmall : (n : ℝ)^(-c) ≤ 1)
    (r k : ℕ) (hrk : 2*r ≤ k) (hk : k ≤ N)
    (hroot : (B.rootClosers (2*r)).card = r)
    (hborn : ∀ v : Fin N, 2*r ≤ v.val → (B.older v).card = 2)
    {a b : Fin N} (hab : a ≠ b) (hne : ¬ B.graph.Adj a b)
    (hmark : k ≤ a.val ∨ k ≤ b.val)
    (hc : B.Covered (Finset.univ.filter (fun x => k ≤ x.val)) a b)
    (hcap : 3 * (N-k) + 1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hscale : (n : ℝ)^(N-k) * prefixDensity n ^ (2*(N-k)+1) ≤ 1) :
    ((graphEmbeddingSet (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((4 * prefixM n)^r * (2 * prefixD n)^(k-2*r)) := by
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
    (B.initialAssignmentSet_bound_unordered hGood hsmall hp r k hrk hk hroot hborn) hκ)

end SharpTerminalLeave.BirthGraph

end

end OAI
