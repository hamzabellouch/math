import OAI.Probability.MatroidSecretary.Accounting.Contracts
import OAI.Probability.MatroidSecretary.Sampling.BernoulliConditionalFiber

namespace OAI

/-!
# Literal conditional expectation in the order-uniform accounting lemma

The canonical accounting contract averages fresh focal bits after fixing all
outside bits. This corollary identifies that average with the normalized
restriction of the full product distribution to the specified outside event.
No order is conditioned on, and all other mask fields remain fixed.
-/

namespace MatroidProphet.AccountingContracts
open Set Finset MainAlgorithm

/-- The fixed-outside test-thinning clause, expressed as a conditional
expectation under the entire independent test-mask law. Every outside atom
has positive mass at the source's interior thinning rate. -/
theorem all_orders_conditional_expectation {n : ℕ}
    (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ)
    (A : Finset (Fin n)) (hA : Disjoint A (pathGroups M d w h)) :
    thinningRate * (finalRankStatistic M hE (2^100)
      (groupMask M d w d.D) (groupMask M d w d.C)
      (fun j => (A : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n)))
      h (groups M d w).length (pathGroups M d w h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) Set.univ
      (boolParity d.odd) : ℝ) ≤
    bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun T => if T \ pathGroups M d w h = A then
        (listedLambda M hE {d with T := T} w h : ℝ) else 0) /
    bitsExpectation (fun _ : Fin n => thinningRate) univ
      (fun T => if T \ pathGroups M d w h = A then 1 else 0) := by
  have hsub : A ⊆ univ \ pathGroups M d w h := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e,
      fun heG => Finset.disjoint_left.mp hA he heG⟩
  rw [bitsExpectation_condition_on_outside_const thinningRate
    (by norm_num [thinningRate]) (by norm_num [thinningRate])
    univ (pathGroups M d w h) A (Finset.subset_univ _) hsub]
  exact (all_orders M hE d w h).2 A hA

end MatroidProphet.AccountingContracts

end OAI
