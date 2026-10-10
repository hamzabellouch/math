import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingEffective
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSingletStarSpectrum

namespace OAI

/-! The crossing construction compared on the complete spin Hilbert space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem qmaCrossingCorrection_star {n : ℕ} (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    (qmaCrossingCorrection site J K).conjTranspose = qmaCrossingCorrection site J K := by
  have hij (a b : Fin 4) (hab : a ≠ b) : site a ≠ site b := fun h => hab (hsite h)
  simp only [qmaCrossingCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    sourceHeisenbergMatrix_star n _ _ (hij 0 1 (by decide)),
    sourceHeisenbergMatrix_star n _ _ (hij 0 3 (by decide)),
    sourceHeisenbergMatrix_star n _ _ (hij 1 2 (by decide)),
    sourceHeisenbergMatrix_star n _ _ (hij 2 3 (by decide)),
    Complex.star_def,Complex.conj_ofReal]
  norm_num [starRingEnd_apply,Complex.star_def]

theorem qmaCrossing_bottom {n r : ℕ} (e : Fin r) (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (R J K : ℝ) (hR : 0 < R)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator ((C + qmaCrossingCorrection site J K) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ a, |qmaCrossingAmplitude R J K a| ≤ epsilon * (4 * R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + qmaCrossingCorrection site J K)
        (qmaSingletStar n r e site qmaCrossingMember (qmaCrossingAmplitude R J K))) -
      sourceMatrixBottom n (C + ((J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2) +
        (K:ℂ) • sourceHeisenbergMatrix n (site 1) (site 3)))| ≤ 16 * R^2 * epsilon^3 := by
  have hCW : (C + qmaCrossingCorrection site J K).conjTranspose =
      C + qmaCrossingCorrection site J K := by
    rw [Matrix.conjTranspose_add,hC,qmaCrossingCorrection_star site hsite]
  have h := qmaSingletStar_bottom n r (sq_pos_of_pos hR) _ hCW e site
    qmaCrossingMember (qmaCrossingAmplitude R J K) hepsilon hsmall hbound
  rw [add_sub_assoc,qmaCrossing_effective e site hsite R J K hR.ne'] at h
  exact h

end ContinuumCoulomb

end

end OAI
