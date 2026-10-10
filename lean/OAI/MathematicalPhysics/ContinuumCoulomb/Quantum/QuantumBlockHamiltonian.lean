import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockExchange

namespace OAI

/-! Literal exchange sums for the real-coefficient four-spin Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

def qmaFourEdgeLeft (e : Fin 6) : Fin 4 := ![0,0,0,1,1,2] e
def qmaFourEdgeRight (e : Fin 6) : Fin 4 := ![1,2,3,2,3,3] e

theorem qmaFourEdge_distinct (e : Fin 6) : qmaFourEdgeLeft e ≠ qmaFourEdgeRight e := by
  fin_cases e <;> decide

theorem qmaFourPenalty_edgeSum : qmaFourPenalty =
    (∑ e : Fin 6, qmaFourExchange (qmaFourEdgeLeft e) (qmaFourEdgeRight e))+
      (6:ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  rw [qmaFourPenalty_exchange]
  simp only [qmaFourEdgeLeft,qmaFourEdgeRight,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  abel

def qmaBlockSourcePenalty (n : ℕ) : Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (∑ i : Fin n, ∑ e : Fin 6, sourceHeisenbergMatrix (n*4)
    (finProdFinEquiv (i,qmaFourEdgeLeft e)) (finProdFinEquiv (i,qmaFourEdgeRight e)))+
      ((n:ℂ)*6) • 1

theorem qmaBlockSourcePenalty_reindex (n : ℕ) :
    (qmaBlockSourcePenalty n).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorPenalty n := by
  simp only [qmaBlockSourcePenalty,MediatorGraph.submatrix_add_apply,MediatorGraph.submatrix_sum,
    MediatorGraph.submatrix_smul_apply,Matrix.submatrix_one_equiv,
    qmaBlockExchange_source _ _ _ (qmaFourEdge_distinct _),qmaFourTensorPenalty,qmaTensorPenalty,
    qmaFourPenalty_edgeSum,qmaSiteMatrix_add,qmaSiteMatrix_sum,qmaSiteMatrix_smul,qmaSiteMatrix_one,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  module

def qmaBlockSourceField (i : Fin n) (x z : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  ((x/(2*Real.sqrt 3):ℝ):ℂ) •
    (sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,3))-
      sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,2)))-
    ((z/2:ℝ):ℂ) • sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,0)) (finProdFinEquiv (i,1))

theorem qmaBlockSourceField_reindex (i : Fin n) (x z : ℝ) :
    (qmaBlockSourceField i x z).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaSiteMatrix i (qmaFourField x z) := by
  simp only [qmaBlockSourceField,Matrix.submatrix_sub,Pi.sub_apply,MediatorGraph.submatrix_smul_apply,
    qmaBlockExchange_source i 0 3 (by decide),qmaBlockExchange_source i 0 2 (by decide),
    qmaBlockExchange_source i 0 1 (by decide),qmaFourField,qmaSiteMatrix_sub,qmaSiteMatrix_smul]

def qmaBlockSourceAxisField (i : Fin n) (a : Fin 2) (t : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  if a = 0 then qmaBlockSourceField i t 0 else qmaBlockSourceField i 0 t

theorem qmaBlockSourceAxisField_reindex (i : Fin n) (a : Fin 2) (t : ℝ) :
    (qmaBlockSourceAxisField i a t).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaSiteMatrix i (qmaFourAxisField a t) := by
  unfold qmaBlockSourceAxisField qmaFourAxisField
  split_ifs <;> exact qmaBlockSourceField_reindex _ _ _

def qmaBlockSourceCoupling (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (qmaFourCouplingSize a b t:ℂ) •
    ∑ p : Fin 4, ∑ q : Fin 4,
      ((qmaFourAxisWeights a true p*qmaFourAxisWeights b (qmaFourCouplingSign t) q:ℝ):ℂ) •
        sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (j,q))

theorem qmaBlockSourceCoupling_reindex (i j : Fin n) (hij : i ≠ j) (a b : Fin 2) (t : ℝ) :
    (qmaBlockSourceCoupling i j a b t).submatrix (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
      qmaFourTensorCoupling i j a b t := by
  simp only [qmaBlockSourceCoupling,MediatorGraph.submatrix_smul_apply,MediatorGraph.submatrix_sum,
    qmaBlockCross_source i j hij,qmaFourTensorCoupling,qmaFourTensorWeighted]

end ContinuumCoulomb

end

end OAI
