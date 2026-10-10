import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkEffective
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingPhysical

namespace OAI

/-! Full-space energy comparison for the rational fork gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

theorem qmaForkCorrection_star {n : ℕ} (site : Fin 3 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    (qmaForkCorrection site J K).conjTranspose = qmaForkCorrection site J K := by
  have hne : site 1 ≠ site 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (hsite h)
  simp only [qmaForkCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one,sourceHeisenbergMatrix_star n _ _ hne,
    Complex.star_def,Complex.conj_ofReal]

theorem qmaFork_bottom {n r : ℕ} (e : Fin r) (site : Fin 3 → Fin n)
    (hsite : Function.Injective site) (R J K : ℝ) (hR : 0 < R)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + qmaForkCorrection site J K) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ a, |qmaForkAmplitude R J K a| ≤ epsilon * (4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + qmaForkCorrection site J K)
        (qmaSingletStar n r e site qmaForkMember (qmaForkAmplitude R J K))) -
      sourceMatrixBottom n (C + ((J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1) +
        (K:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2)))| ≤ 16*R^2*epsilon^3 := by
  have hCW : (C + qmaForkCorrection site J K).conjTranspose =
      C + qmaForkCorrection site J K := by
    rw [Matrix.conjTranspose_add,hC,qmaForkCorrection_star site hsite]
  have h := qmaSingletStar_bottom n r (sq_pos_of_pos hR) _ hCW e site
    qmaForkMember (qmaForkAmplitude R J K) hepsilon hsmall hbound
  rw [add_sub_assoc,qmaFork_effective e site hsite R J K hR.ne'] at h
  exact h

end ContinuumCoulomb

end

end OAI
