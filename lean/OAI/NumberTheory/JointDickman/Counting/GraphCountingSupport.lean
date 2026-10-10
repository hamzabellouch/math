import OAI.NumberTheory.JointDickman.Probability.NormalizedGraphKernel
import OAI.NumberTheory.JointDickman.Amplification.GraphEdgeMajorant
import OAI.NumberTheory.JointDickman.Amplification.GraphTripleSupport

namespace OAI

/-! # The original finite graph is supported at the counting scale -/
namespace JointDickman
open Finset Classical

theorem graphTriple_edge_counting_bound {B L T N n : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (he : n ∈ graphTripleEdges N g)
    (hw : graphTripleWeight B L τ C T g n ≠ 0) : n < 2*T*N := by
  have hs := graphTripleWeight_nonzero_supported hB hT τ C hg rfl hw
  have hsub := graphTriple_subsets hg
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hsub.2.1 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hsub.1 hp)).pos)
  have hrel := (mem_filter.mp hg).2
  have hb := ((mem_amplificationCoefficientPairs hB).mp (mem_filter.mp hs).2.2.2).2.2.2
  exact divisorEdge_small_endpoint ha hc hrel.2.2.2.1 hrel.2.2.2.2
    (by simpa only [graphTriplePair,mul_assoc] using hb) he

theorem rawArithmeticGraphKernel_counting_support {B L T N n : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (j : ℤ) (hn : 2*T*N ≤ n) :
    rawArithmeticGraphKernel B L τ C T N j n = 0 := by
  unfold rawArithmeticGraphKernel
  apply sum_eq_zero
  intro g hg
  split_ifs with hh
  · by_contra hw
    exact (not_lt_of_ge hn) (graphTriple_edge_counting_bound hB hT hg hh.2 hw)
  · rfl

theorem finiteGraphKernel_counting_support {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hu : 2*T*N ≤ u) :
    finiteGraphKernel B L T H M N u τ C = fun _ _ => 0 := by
  funext i k
  unfold finiteGraphKernel
  split_ifs
  · rw [rawArithmeticGraphKernel_counting_support hB hT _ (by omega),zero_div]
  · rfl

end JointDickman

end OAI
