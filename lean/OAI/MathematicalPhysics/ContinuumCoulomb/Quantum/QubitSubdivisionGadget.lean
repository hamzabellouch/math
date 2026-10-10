import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionGround
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionCalibration

namespace OAI

/-! The actual simultaneous subdivision gadget has inverse-polynomial error
at an explicit polynomial choice of rational coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaSubdivision_polynomial_accuracy (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {b N : ℝ} (hb : 0 ≤ b) (hN : 1 ≤ N)
    (hH : H.conjTranspose = H) (hHnorm : ‖spinMatrixOperator H‖ ≤ b)
    (hAstar : ∀ e, (A e).conjTranspose = A e) (hBstar : ∀ e, (B e).conjTranspose = B e)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    let R := 8*(qmaThirdBudget b J)^4*N
    |MediatorGraph.normalizedBottom (qmaSubdivisionGadget H A B R J)-
      MediatorGraph.normalizedBottom (qmaSubdivisionTarget H A B (fun e => J e))| ≤ 1/N := by
  let K := qmaThirdBudget b J
  have hK : 1 ≤ K := qmaThirdBudget_pos hb J
  have hR := (Perturbation.thirdOrder_polynomial_schedule hK hN).1
  have hr : 1 ≤ 8*K^4*N := by linarith
  have hAnorm (e : κ) : ‖spinMatrixOperator (A e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hAstar,hA]
  have hBnorm (e : κ) : ‖spinMatrixOperator (B e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hBstar,hB]
  obtain ⟨hL,hPsq,hTarget,hPert,hCouple⟩ :=
    qmaSubdivision_calibration H A B J hb hr hHnorm hAnorm hBnorm
  have he := qmaSubdivision_target_ground H A B J hK hR hA hB hAB
    (fun e => by simpa only [Complex.ofReal_neg] using
      qmaThirdPair_star (A e) (B e) (-J e) (hAstar e) (hBstar e))
    (qmaSubdivisionLow_star H J hH) hL hPsq hTarget hPert hCouple u hu
  apply he.trans
  have hNp : 0 < N := by linarith
  have hKp : 0 < K := by linarith
  change 7*K^4/(8*K^4*N) ≤ 1/N
  have heq : 7*K^4/(8*K^4*N) = (7/8:ℝ)/N := by field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right (by norm_num) hNp.le

end ContinuumCoulomb

end

end OAI
