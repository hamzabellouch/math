import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdHermitian
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorTargetGround

namespace OAI

/-! An explicit parallel third-order gadget with a polynomial accuracy scale. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaThirdGadget (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalMediatorMatrix (R^3) (qmaThirdSeriesLow H A B C R (fun e => J e))
    (fun e => (R^2:ℝ) • C e)
    (fun e => (R^2:ℝ) • qmaThirdSeriesPair (A e) (B e) (J e))

theorem qmaThirdGadget_error (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {b R : ℝ} (hb : 0 ≤ b)
    (hR : 4*qmaThirdBudget b J ≤ R)
    (hH : H.conjTranspose = H) (hHnorm : ‖spinMatrixOperator H‖ ≤ b)
    (hAstar : ∀ e, (A e).conjTranspose = A e)
    (hBstar : ∀ e, (B e).conjTranspose = B e)
    (hCstar : ∀ e, (C e).conjTranspose = C e)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1) (hC : ∀ e, C e*C e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J)-
      MediatorGraph.normalizedBottom (qmaThirdSeriesTarget H A B C (fun e => J e))| ≤
        5*(qmaThirdBudget b J)^4/R := by
  have hK : 1 ≤ qmaThirdBudget b J := qmaThirdBudget_pos hb J
  have hr : 1 ≤ R := by linarith
  have hAnorm (e : κ) : ‖spinMatrixOperator (A e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hAstar,hA]
  have hBnorm (e : κ) : ‖spinMatrixOperator (B e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hBstar,hB]
  have hCnorm (e : κ) : ‖spinMatrixOperator (C e)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    rw [hCstar,hC]
  obtain ⟨hL,hPsq,hTarget,hPert,hCouple⟩ :=
    qmaThirdFamily_calibration H A B C J hb hr hHnorm hAnorm hBnorm hCnorm
  exact qmaThirdSeries_target_ground H A B C (fun e => J e) hK hR hA hB hAB hAC hBC
    hCstar (fun e => qmaThirdPair_star (A e) (B e) (J e) (hAstar e) (hBstar e))
    (qmaThirdLow_star H A B C R J hH hAstar hBstar hCstar hAB)
    hL hPsq hTarget hPert hCouple u hu

theorem qmaThirdGadget_polynomial_accuracy (H : Matrix σ σ ℂ)
    (A B C : κ → Matrix σ σ ℂ) (J : κ → ℝ) {b N : ℝ} (hb : 0 ≤ b) (hN : 1 ≤ N)
    (hH : H.conjTranspose = H) (hHnorm : ‖spinMatrixOperator H‖ ≤ b)
    (hAstar : ∀ e, (A e).conjTranspose = A e)
    (hBstar : ∀ e, (B e).conjTranspose = B e)
    (hCstar : ∀ e, (C e).conjTranspose = C e)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1) (hC : ∀ e, C e*C e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    let R := 8*(qmaThirdBudget b J)^4*N
    |MediatorGraph.normalizedBottom (qmaThirdGadget H A B C R J)-
      MediatorGraph.normalizedBottom (qmaThirdSeriesTarget H A B C (fun e => J e))| ≤ 1/N := by
  let K := qmaThirdBudget b J
  have hK : 1 ≤ K := qmaThirdBudget_pos hb J
  have hR := (Perturbation.thirdOrder_polynomial_schedule hK hN).1
  have he := qmaThirdGadget_error H A B C J hb hR hH hHnorm hAstar hBstar hCstar
    hA hB hC hAB hAC hBC u hu
  apply he.trans
  have hNp : 0 < N := by linarith
  have hKp : 0 < K := by linarith
  change 5*K^4/(8*K^4*N) ≤ 1/N
  have heq : 5*K^4/(8*K^4*N) = (5/8:ℝ)/N := by field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right (by norm_num) hNp.le

end ContinuumCoulomb

end

end OAI
