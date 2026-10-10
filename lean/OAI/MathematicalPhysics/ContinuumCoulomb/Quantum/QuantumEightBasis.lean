import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCross
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph

namespace OAI

/-! The two encoded blocks are eight ordinary physical spins. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaEightBasisEquiv : (Fin 8 → Fin 2) ≃ (Fin 16 × Fin 16) where
  toFun s := (qmaFourIndex (fun i => s (Fin.castAdd 4 i)),
    qmaFourIndex (fun i => s (Fin.natAdd 4 i)))
  invFun p k := Fin.addCases (motive := fun _ : Fin (4+4) => Fin 2)
    (qmaFourBits p.1) (qmaFourBits p.2) k
  left_inv s := by
    funext k
    refine Fin.addCases (m := 4) (n := 4) (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.addCases_left]
      exact congrFun (qmaFourBasisEquiv.symm_apply_apply (fun j => s (Fin.castAdd 4 j))) i
    · simp only [Fin.addCases_right]
      exact congrFun (qmaFourBasisEquiv.symm_apply_apply (fun j => s (Fin.natAdd 4 j))) i
  right_inv p := by
    simp only [Fin.addCases_left,Fin.addCases_right]
    exact Prod.ext (qmaFourBasisEquiv.apply_symm_apply p.1) (qmaFourBasisEquiv.apply_symm_apply p.2)

theorem qmaEightTensor_source (M : Fin 8 → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor 8 M).submatrix qmaEightBasisEquiv.symm qmaEightBasisEquiv.symm =
      (sourceTensor 4 (fun i => M (Fin.castAdd 4 i))).submatrix qmaFourBits qmaFourBits ⊗ₖ
      (sourceTensor 4 (fun i => M (Fin.natAdd 4 i))).submatrix qmaFourBits qmaFourBits := by
  ext p q
  change (∏ i : Fin (4+4), M i (qmaEightBasisEquiv.symm p i) (qmaEightBasisEquiv.symm q i)) =
    (∏ i : Fin 4, M (Fin.castAdd 4 i) (qmaFourBits p.1 i) (qmaFourBits q.1 i))*
    ∏ i : Fin 4, M (Fin.natAdd 4 i) (qmaFourBits p.2 i) (qmaFourBits q.2 i)
  rw [Fin.prod_univ_add]
  simp only [qmaEightBasisEquiv,Equiv.coe_fn_symm_mk,Fin.addCases_left,Fin.addCases_right]

theorem qmaEightPauli_left (i : Fin 4) (μ : Fin 3) :
    (sourceLocalPauli 8 (Fin.castAdd 4 i) μ).submatrix qmaEightBasisEquiv.symm qmaEightBasisEquiv.symm =
      qmaFourSpin i μ ⊗ₖ (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  rw [sourceLocalPauli,qmaEightTensor_source]
  have hL : (fun k : Fin 4 => if Fin.castAdd 4 k = Fin.castAdd 4 i then pauli μ else 1) =
      (fun k => if k = i then pauli μ else 1) := by
    funext k
    have he : Fin.castAdd 4 k = Fin.castAdd 4 i ↔ k = i := by
      simp only [Fin.ext_iff,Fin.val_castAdd]
    simp only [he]
  have hR : (fun k : Fin 4 => if Fin.natAdd 4 k = Fin.castAdd 4 i then pauli μ else 1) =
      (fun _ => 1) := by
    funext k
    have hne : Fin.natAdd 4 k ≠ Fin.castAdd 4 i := by
      intro h
      have hv := congrArg Fin.val h
      have hi := i.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    rw [ite_eq_right hne]
  rw [hL,hR,sourceTensor_one]
  change (sourceLocalPauli 4 i μ).submatrix qmaFourBits qmaFourBits ⊗ₖ
    (1 : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ).submatrix qmaFourBits qmaFourBits = _
  rw [← qmaFourSpin_source]
  congr 1
  ext s t
  have he : qmaFourBits s = qmaFourBits t ↔ s = t := qmaFourBasisEquiv.symm.injective.eq_iff
  simp only [Matrix.submatrix_apply,Matrix.one_apply,he]

theorem qmaEightPauli_right (i : Fin 4) (μ : Fin 3) :
    (sourceLocalPauli 8 (Fin.natAdd 4 i) μ).submatrix qmaEightBasisEquiv.symm qmaEightBasisEquiv.symm =
      (1 : Matrix (Fin 16) (Fin 16) ℂ) ⊗ₖ qmaFourSpin i μ := by
  rw [sourceLocalPauli,qmaEightTensor_source]
  have hR : (fun k : Fin 4 => if Fin.natAdd 4 k = Fin.natAdd 4 i then pauli μ else 1) =
      (fun k => if k = i then pauli μ else 1) := by
    funext k
    have he : Fin.natAdd 4 k = Fin.natAdd 4 i ↔ k = i := by
      simp only [Fin.ext_iff,Fin.val_natAdd,Nat.add_left_cancel_iff]
    simp only [he]
  have hL : (fun k : Fin 4 => if Fin.castAdd 4 k = Fin.natAdd 4 i then pauli μ else 1) =
      (fun _ => 1) := by
    funext k
    have hne : Fin.castAdd 4 k ≠ Fin.natAdd 4 i := by
      intro h
      have hv := congrArg Fin.val h
      have hk := k.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    rw [ite_eq_right hne]
  rw [hL,hR,sourceTensor_one]
  change (1 : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ).submatrix qmaFourBits qmaFourBits ⊗ₖ
    (sourceLocalPauli 4 i μ).submatrix qmaFourBits qmaFourBits = _
  rw [← qmaFourSpin_source]
  congr 1
  ext s t
  have he : qmaFourBits s = qmaFourBits t ↔ s = t := qmaFourBasisEquiv.symm.injective.eq_iff
  simp only [Matrix.submatrix_apply,Matrix.one_apply,he]

theorem qmaFourCross_source (i j : Fin 4) :
    (sourceHeisenbergMatrix 8 (Fin.castAdd 4 i) (Fin.natAdd 4 j)).submatrix
      qmaEightBasisEquiv.symm qmaEightBasisEquiv.symm = qmaFourCross i j := by
  have hij : Fin.castAdd 4 i ≠ Fin.natAdd 4 j := by
    intro h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  rw [← sourceLocalPauli_sum 8 _ _ hij,MediatorGraph.submatrix_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [← Matrix.submatrix_mul_equiv _ _ _ qmaEightBasisEquiv.symm _,qmaEightPauli_left,qmaEightPauli_right,
    ← Matrix.mul_kronecker_mul,Matrix.mul_one,Matrix.one_mul]

end ContinuumCoulomb

end

end OAI
