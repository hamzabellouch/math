import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFullFamily

namespace OAI

/-! The tensor code's physical coordinates are exactly ordinary groups of four qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaBlockBasisEquiv (n : ℕ) : SourceSpinBasis (n*4) ≃ (Fin n → Fin 16) where
  toFun s i := qmaFourBasisEquiv (fun p => s (finProdFinEquiv (i,p)))
  invFun x k := qmaFourBasisEquiv.symm (x (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
  left_inv s := by
    funext k
    obtain ⟨⟨i,p⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply]

theorem qmaBlockBasisEquiv_symm_site (n : ℕ) (x : Fin n → Fin 16) (i : Fin n) (p : Fin 4) :
    (qmaBlockBasisEquiv n).symm x (finProdFinEquiv (i,p)) = qmaFourBits (x i) p := by
  change qmaFourBasisEquiv.symm (x (finProdFinEquiv.symm (finProdFinEquiv (i,p))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i,p))).2 = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem qmaBlockTensor_source (n : ℕ) (A : Fin n → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor (n*4) (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm =
        qmaTensorMatrix (fun i => (sourceTensor 4 (A i)).submatrix qmaFourBits qmaFourBits) := by
  ext x y
  change (∏ k : Fin (n*4), A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    ((qmaBlockBasisEquiv n).symm x k) ((qmaBlockBasisEquiv n).symm y k)) =
    ∏ i, ∏ p, A i p (qmaFourBits (x i) p) (qmaFourBits (y i) p)
  rw [← finProdFinEquiv.prod_comp]
  simp only [Equiv.symm_apply_apply,qmaBlockBasisEquiv_symm_site,Fintype.prod_prod_type]

theorem qmaBlockPauli_source (n : ℕ) (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    (sourceLocalPauli (n*4) (finProdFinEquiv (i,p)) μ).submatrix
      (qmaBlockBasisEquiv n).symm (qmaBlockBasisEquiv n).symm = qmaSiteMatrix i (qmaFourSpin p μ) := by
  have hsource : sourceLocalPauli (n*4) (finProdFinEquiv (i,p)) μ =
      sourceTensor (n*4) (fun k => if (finProdFinEquiv.symm k).1 = i then
        (if (finProdFinEquiv.symm k).2 = p then pauli μ else 1) else 1) := by
    unfold sourceLocalPauli
    congr 1
    funext k
    obtain ⟨⟨j,q⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
    by_cases hj : j = i <;> by_cases hq : q = p <;> simp [hj,hq]
  rw [hsource,qmaBlockTensor_source n (fun j q => if j = i then (if q = p then pauli μ else 1) else 1),qmaSiteMatrix]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ite_true,qmaFourSpin_source,sourceLocalPauli]
  · simp only [hj,ite_false,sourceTensor_one]
    exact Matrix.submatrix_one_equiv qmaFourBasisEquiv.symm

end ContinuumCoulomb

end

end OAI
