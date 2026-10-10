import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges
import OAI.Combinatorics.TriangleRemoval.Process.PlusEdgesSimple
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderEmbRank
import OAI.Combinatorics.TriangleRemoval.Coupling.InitialAssignmentSetBound
import OAI.Combinatorics.TriangleRemoval.Process.SeedEdgeSubsetPath
import OAI.Combinatorics.TriangleRemoval.Process.SuffixProjection

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma backEdges_card_split (R : ℕ) (hR : R ≤ N)
    (hborn : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2) :
    (B.backEdges Finset.univ).card =
      (B.backEdges (initialVertices N R)).card + 2*(N-R) := by
  classical
  rw [B.backEdges_card,B.backEdges_card]
  have hsum := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun v => v.val < R) (fun v => (B.older v).card)
  have hborn' : (∑ v ∈ Finset.univ.filter (fun v : Fin N => ¬v.val < R), (B.older v).card) =
      2*(N-R) := by
    have he : (∑ v ∈ Finset.univ.filter (fun v : Fin N => ¬v.val < R), (B.older v).card) =
        ∑ _v ∈ Finset.univ.filter (fun v : Fin N => ¬v.val < R), 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hborn v (Nat.le_of_not_gt (Finset.mem_filter.mp hv).2)
    rw [he,Finset.sum_const,smul_eq_mul]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun v => v.val < R)
    rw [Fin.card_filter_val_lt,Nat.min_eq_right hR,Finset.card_univ,Fintype.card_fin] at hc
    have hf : (Finset.univ.filter (fun v : Fin N => ¬v.val < R)).card = N-R := by omega
    rw [hf,Nat.mul_comm]
  rw [hborn'] at hsum
  exact hsum.symm

end BirthGraph

lemma witness_scale_identity (n r s : ℕ) :
    (n : ℝ)^(2*r+s) * prefixDensity n^(r+2*s+1) =
      (2*prefixM n)^r * prefixD n^s * prefixDensity n := by
  unfold prefixM prefixD
  have he : 2*((n : ℝ)^2 * prefixDensity n / 2) = (n : ℝ)^2 * prefixDensity n := by ring
  rw [he,pow_add,pow_add,pow_add,mul_pow,mul_pow]
  rw [pow_mul,pow_mul]
  ring

namespace TriangleGrowth
variable {n N r : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N (2*r))

lemma pathPattern_edge_card (a b : Fin N) (hR : 2*r ≤ N)
    (hseed : (A.seed.backEdges A.roots).card = r) :
    ((A.pathPattern a b).backEdges Finset.univ).card = r+2*(A.pathSuffix a b (2*r)).card := by
  rw [(A.pathPattern a b).backEdges_card_split (2*r)
    (roots_le_card _ hR (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)))
    (A.pathPattern_nonroot a b)]
  rw [A.pathPattern_rootEdges a b hR,A.pathRootEdges_card,hseed,A.path_card_split a b hR]
  omega

theorem actual_short_witness_count {c C : ℝ} (hGood : GoodPrefixGraph n c C G)
    (a b : Fin N) (hR : 2*r ≤ N) (hseed : (A.seed.backEdges A.roots).card = r)
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b)
    (hcap : (A.pathUnion a b).card ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n) :
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((2*prefixM n)^r *
        prefixD n^(A.pathSuffix a b (2*r)).card * prefixDensity n) := by
  have hex := A.pathPattern_extra he
  have h := (A.pathPattern a b).short_witness_count hGood hex.1 hex.2 hcap hp hp1 hD
  rw [A.pathPattern_edge_card a b hR hseed] at h
  conv at h => rhs; rw [A.path_card_split a b hR,witness_scale_identity]
  exact h

theorem actual_long_witness_count {c C : ℝ} (hGood : GoodPrefixGraph n c C G)
    (hsmall : (n : ℝ)^(-c) ≤ 1) (a b : Fin N) (hR : 2*r ≤ N)
    (hseed : (A.seed.backEdges A.roots).card = r)
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b)
    (k : ℕ) (hrk : 2*r ≤ k) (hk : k < (A.pathUnion a b).card)
    (hcap : 3*((A.pathUnion a b).card-k)+1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hscale : (n : ℝ)^((A.pathUnion a b).card-k) *
      prefixDensity n^(2*((A.pathUnion a b).card-k)+1) ≤ 1) :
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((4*prefixM n)^r * (2*prefixD n)^(k-2*r)) := by
  have hex := A.pathPattern_extra he
  apply (A.pathPattern a b).long_witness_count_unordered hGood hsmall r k hrk hk.le
  · rw [A.pathPattern_rootClosers a b hR,hseed]
  · exact A.pathPattern_nonroot a b
  · exact hex.1
  · exact hex.2
  · exact A.path_mark_reaches_suffix a b k hrk hk
  · exact A.pathPattern_covered a b k hrk hk
  · exact hcap
  · exact hp
  · exact hp1
  · exact hD
  · exact hscale

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
