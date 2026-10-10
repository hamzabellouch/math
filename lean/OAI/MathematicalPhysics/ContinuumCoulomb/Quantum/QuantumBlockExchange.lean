import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockBasis

namespace OAI

/-! Both internal and cross-block couplings are ordinary source Heisenberg exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaBlockExchange_source (i : Fin n) (p q : Fin 4) (hpq : p ≠ q) :
    (sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (i,q))).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaSiteMatrix i (qmaFourExchange p q) := by
  have hij : finProdFinEquiv (i,p) ≠ finProdFinEquiv (i,q) := by
    intro h
    exact hpq (congrArg Prod.snd (finProdFinEquiv.injective h))
  rw [← sourceLocalPauli_sum (n*4) _ _ hij,MediatorGraph.submatrix_sum,
    qmaFourExchange_pauli p q hpq,qmaSiteMatrix_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ (qmaBlockBasisEquiv n).symm _,
    qmaBlockPauli_source,qmaBlockPauli_source,qmaSiteMatrix_mul]

theorem qmaBlockCross_source (i j : Fin n) (hij : i ≠ j) (p q : Fin 4) :
    (sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (j,q))).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaFourTensorCross i j p q := by
  have hne : finProdFinEquiv (i,p) ≠ finProdFinEquiv (j,q) := by
    intro h
    exact hij (congrArg Prod.fst (finProdFinEquiv.injective h))
  rw [← sourceLocalPauli_sum (n*4) _ _ hne,MediatorGraph.submatrix_sum,qmaFourTensorCross]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ (qmaBlockBasisEquiv n).symm _,
    qmaBlockPauli_source,qmaBlockPauli_source]

end ContinuumCoulomb

end

end OAI
