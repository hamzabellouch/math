import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateBoundaryBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateDyadic
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNormBlocks

namespace OAI

namespace Ostmann.QuadraticSieve

theorem dual_zero_large_partition_bound (K N : ℕ) (hN : 0<N)
    (F : ℕ → ℕ → ℂ) (B : ℝ)
    (hfirst : ∀ j ∈ Finset.range (Nat.log 2 K+1),
      ‖∑ v ∈ binarySquarefreeRows K j, F 1 v‖≤B)
    (hblocks : ∀ j ∈ Finset.range (Nat.log 2 K+1),
      ∀ k ∈ Finset.range (Nat.log 2 (N^2)+1),
        ‖∑ d ∈ Finset.Ioc (2^k) (2*2^k), ∑ v ∈ binarySquarefreeRows K j,
          if d≤N^2 then F d v else 0‖≤B) :
    ‖∑ v ∈ oddSquarefreeUpTo K, ∑ d ∈ Finset.Icc 1 (N^2), F d v‖ ≤
      (Nat.log 2 K+1:ℕ)*(Nat.log 2 (N^2)+2:ℕ)*B := by
  rw [sum_oddSquarefree_eq_dyadic]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 K+1), (Nat.log 2 (N^2)+2:ℕ)*B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.sum_comm]
      apply norm_sum_Icc_one_le_boundary_dyadic (N^2) (by positivity) _ B (hfirst j hj)
      intro k hk
      simpa only [aggregateDivisorBlock,Finset.sum_filter,Finset.sum_ite_irrel,
        Finset.sum_const_zero] using hblocks j hj k hk
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end Ostmann.QuadraticSieve

end OAI
