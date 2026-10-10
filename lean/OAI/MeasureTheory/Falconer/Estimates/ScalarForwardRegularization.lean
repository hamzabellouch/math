import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialRegularization

namespace OAI

/-! The initial scalar regularization in increasing geometric depth.
 Exact full blocks are the form used in the porous/nonporous dichotomy. -/
namespace Falconer.Regularization

 theorem blockDepth_product (B M i : ℕ) (hi : i ≤ M) :
    blockDepth (B*M) B (M-i) = B*i := by
  unfold blockDepth
  rw [Nat.mul_comm (M-i) B,← Nat.mul_sub_left_distrib,Nat.sub_sub_self hi]

 theorem scalar_forward_regularization {B M : ℕ} (hB : 0 < B)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty) :
    ∃ Q : Finset (CellPath 1), ∃ k n : ℕ → ℕ,
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ (2050*(B+1)^2)^(M+1)*Q.card ∧
      ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (k i) (n i) := by
  obtain ⟨Q,k,n,hQne,hQL,hsize,hlevels⟩ := scalar_initial_regularization L hL hne B
  have hdiv : B*M/B = M := by rw [Nat.mul_comm B M,Nat.mul_div_cancel _ hB]
  rw [hdiv] at hsize hlevels
  refine ⟨Q,fun i => k (M-i-1),fun i => n (M-i-1),hQne,hQL,hsize,?_⟩
  intro i hi
  have hj : M-i-1 < M+1 := by omega
  have hh := hlevels (M-i-1) hj
  have hleft : blockDepth (B*M) B (M-i-1+1) = B*i := by
    rw [show M-i-1+1 = M-i by omega]
    exact blockDepth_product B M i (by omega)
  have hright : blockDepth (B*M) B (M-i-1) = B*(i+1) := by
    rw [show M-i-1 = M-(i+1) by omega]
    exact blockDepth_product B M (i+1) (by omega)
  rwa [hleft,hright] at hh

end Falconer.Regularization

end OAI
