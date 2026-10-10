import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.GraphStarApproximation
import OAI.Combinatorics.TriangleRemoval.Process.LinkSimpleGraph

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

theorem goodPrefix_star_approximation {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (u : Fin n) [Nonempty (neighbors G u)]
    (j : ℕ) (hj : j+3 ≤ prefixCycleCap) (heven : Even (j+3))
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ - averagingProjector‖ ≤
      4 * (((j+4 : ℕ) : ℝ) * (n : ℝ)^(-c) + ((j+3 : ℕ) : ℝ)^(j+4) * 2^(j+3) *
        ((neighbors G u).card / prefixD n^((j+3)/2) + 1/prefixD n)) ^
          (1 / ((j+3 : ℕ) : ℝ)) + 7*(n : ℝ)^(-c) := by
  have hc := h.2.2.2.2.1
  have hmain := hc (j+3) (by omega) hj u
  rw [linkCycleCount_eq_graphEmbeddings (j := j+1) G h.1 u] at hmain
  have hcyc : ∀ b, 3 ≤ b → b < j+3 →
      ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G h.1 u)).card : ℝ) ≤
        2 * prefixD n ^ b := by
    intro b hb hbj
    have hh := (abs_le.mp (hc b hb (by omega) u)).2
    have heq : b = b-2+2 := by omega
    have hcount : linkCycleCount b G u =
        ((graphEmbeddings (SimpleGraph.cycleGraph b) (linkSimpleGraph G h.1 u)).card : ℝ) := by
      rw [heq]
      exact linkCycleCount_eq_graphEmbeddings G h.1 u
    rw [hcount] at hh
    have hx := mul_le_mul_of_nonneg_right hδ (pow_nonneg (le_trans zero_le_one hD) b)
    nlinarith
  simpa only [Fintype.card_coe] using graph_star_approximation (linkSimpleGraph G h.1 u)
    j heven (prefixD n) ((n : ℝ)^(-c)) hD (Real.rpow_nonneg (Nat.cast_nonneg _) _) hδ
    (goodPrefix_link_rows h u) hmain hcyc

theorem goodPrefix_star_fixed {n : ℕ} {G : Graph n} {c C : ℝ}
    (h : GoodPrefixGraph n c C G) (u : Fin n) [Nonempty (neighbors G u)]
    (hD : 1 ≤ prefixD n) (hδ : (n : ℝ)^(-c) ≤ 1) :
    ‖(prefixD n)⁻¹ • (linkSimpleGraph G h.1 u).adjMatrix ℝ - averagingProjector‖ ≤
      4 * ((8001 : ℝ) * (n : ℝ)^(-c) + (8000 : ℝ)^8001 * 2^8000 *
        ((neighbors G u).card / prefixD n^4000 + 1/prefixD n)) ^ (1 / (8000 : ℝ)) +
        7*(n : ℝ)^(-c) := by
  exact goodPrefix_star_approximation h u 7997 (by decide) (by decide) hD hδ

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

end
end

end OAI
