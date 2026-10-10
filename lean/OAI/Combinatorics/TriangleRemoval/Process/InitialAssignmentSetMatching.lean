import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Process.InitialAssignmentSet
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddingsAfterRoots
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraphDegree
import OAI.Combinatorics.TriangleRemoval.Process.OrientedEdges

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

theorem initialAssignmentSet_matching_bound {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hsmall : (n : ℝ)^(-c) ≤ 1)
    (r k : ℕ) (hrk : 2*r ≤ k) (hk : k ≤ N)
    (u v : Fin r → Fin (2*r))
    (hcover : ∀ i : Fin (2*r), ∃ j, i = u j ∨ i = v j)
    (hroot : ∀ j, B.graph.Adj (Fin.castLE (hrk.trans hk) (u j))
      (Fin.castLE (hrk.trans hk) (v j)))
    (hborn : ∀ x : Fin N, 2*r ≤ x.val → (B.older x).card = 2) :
    ((B.initialAssignmentSet G k hk).card : ℝ) ≤
      (2 * prefixM n)^r * (2 * prefixD n)^(k-2*r) := by
  classical
  have hD0 : 0 ≤ 2 * prefixD n := by unfold prefixD; positivity
  have hsimple : ∀ e ∈ G, e.card = 2 := by
    intro e he
    exact (Finset.mem_powersetCard.mp (hGood.1 he)).2
  have hgrow := prefixEmbeddings_after_roots B.graph (lookupGraph G) (2*r) k hrk hk
    (2 * prefixD n) hD0 (goodPrefix_codegree_bound hGood hsmall)
    (fun i hi hN => B.two_preceding_neighbors (2*r) hborn i hi hN)
  have hroots := prefixEmbeddings_root_cover B.graph G hsimple (hrk.trans hk) u v hcover hroot
  have hrootsR : ((prefixEmbeddings B.graph (lookupGraph G) (2*r) (hrk.trans hk)).card : ℝ) ≤
      (2 * prefixM n)^r := by
    have hh : ((prefixEmbeddings B.graph (lookupGraph G) (2*r) (hrk.trans hk)).card : ℝ) ≤
        (2 * (G.card : ℝ))^r := by exact_mod_cast hroots
    rwa [hGood.2.1] at hh
  exact (Nat.cast_le.mpr (B.initialAssignmentSet_card G k hk)).trans
    (hgrow.trans (mul_le_mul_of_nonneg_right hrootsR (pow_nonneg hD0 _)))

end SharpTerminalLeave.BirthGraph

end

end OAI
