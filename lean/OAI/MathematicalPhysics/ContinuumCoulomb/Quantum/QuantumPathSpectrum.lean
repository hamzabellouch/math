import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSubdivision

namespace OAI

/-! The even and odd rational subdivision gadgets on the full spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker

theorem qmaPathSubdivision_bottom {n r : ℕ} (e : Fin r) (site : Fin 2 → Fin n)
    (hsite : Function.Injective site) (even : Bool) (R J : ℝ) (hR : 0 < R)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + qmaPathCorrection (n := n) R J) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ a, |qmaPathAmplitude even R J a| ≤ epsilon*(4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + qmaPathCorrection (n := n) R J)
        (qmaSingletStar n r e site (qmaPathMember even) (qmaPathAmplitude even R J))) -
      sourceMatrixBottom n (C + (J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 1))| ≤
      16*R^2*epsilon^3 := by
  have hCC : (C + qmaPathCorrection (n := n) R J).conjTranspose = C + qmaPathCorrection (n := n) R J := by
    simp only [qmaPathCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one,hC,Complex.star_def,Complex.conj_ofReal]
  have h := qmaSingletStar_bottom n r (sq_pos_of_pos hR) _ hCC e site
    (qmaPathMember even) (qmaPathAmplitude even R J) hepsilon hsmall hbound
  rw [add_sub_assoc,qmaPathSubdivision_effective e site hsite even R J hR.ne'] at h
  exact h

end ContinuumCoulomb

end

end OAI
