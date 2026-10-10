import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionMatrix

namespace OAI

/-! The subdivision counterterm is scalar, Hermitian and polynomially bounded. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [Fintype σ] in
theorem qmaSubdivisionCounter_real (j : ℝ) : qmaSubdivisionCounter (ι := σ) (j:ℂ) =
    (1+(j/2)^2:ℝ) • (1 : Matrix σ σ ℂ) := by
  unfold qmaSubdivisionCounter
  change (1+(-(j:ℂ)/2)^2) • (1 : Matrix σ σ ℂ) = ((1+(j/2)^2:ℝ):ℂ) • 1
  congr 1
  push_cast
  ring

omit [Fintype σ] in
theorem qmaSubdivisionCounter_star (j : ℝ) :
    (qmaSubdivisionCounter (ι := σ) (j:ℂ)).conjTranspose = qmaSubdivisionCounter (j:ℂ) := by
  rw [qmaSubdivisionCounter_real]
  simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.conjTranspose_one]

omit [Fintype σ] [DecidableEq κ] in
theorem qmaSubdivisionLow_star (H : Matrix σ σ ℂ) (J : κ → ℝ) (hH : H.conjTranspose = H) :
    (qmaSubdivisionLow H (fun e => J e)).conjTranspose = qmaSubdivisionLow H (fun e => J e) := by
  simp only [qmaSubdivisionLow,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hH,
    qmaSubdivisionCounter_star]

theorem qmaSubdivisionCounter_norm (j : ℝ) :
    ‖spinMatrixOperator (qmaSubdivisionCounter (ι := σ) (j:ℂ))‖ ≤ qmaThirdWeight j := by
  rw [qmaSubdivisionCounter_real,qmaMatrix_real_smul_norm,abs_of_nonneg (by positivity)]
  have hI : ‖spinMatrixOperator (1 : Matrix σ σ ℂ)‖ ≤ 1 :=
    spinMatrixOperator_unitary_norm _ (by simp)
  have h := mul_le_mul_of_nonneg_left hI (show (0:ℝ) ≤ 1+(j/2)^2 by positivity)
  have hw := (qmaThirdWeight_bounds j).2.2.1
  simp only [mul_one] at h
  linarith [abs_nonneg j]

omit [DecidableEq κ] in
theorem qmaSubdivisionLow_norm (H : Matrix σ σ ℂ) (J : κ → ℝ)
    {b : ℝ} (hH : ‖spinMatrixOperator H‖ ≤ b) :
    ‖spinMatrixOperator (qmaSubdivisionLow H (fun e => J e))‖ ≤ b+∑ e, qmaThirdWeight (J e) := by
  unfold qmaSubdivisionLow
  rw [spinMatrixOperator_add,spinMatrixOperator_sum]
  apply (norm_add_le _ _).trans
  apply add_le_add hH
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaSubdivisionCounter_norm (σ := σ) (J e)))

omit [DecidableEq κ] in
theorem qmaSubdivisionTarget_norm (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    {b : ℝ} (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1) (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1) :
    ‖spinMatrixOperator (qmaSubdivisionTarget H A B (fun e => J e))‖ ≤ b+∑ e, qmaThirdWeight (J e) := by
  have hc (e : κ) : ‖spinMatrixOperator (1 : Matrix σ σ ℂ)‖ ≤ 1 :=
    spinMatrixOperator_unitary_norm _ (by simp)
  simpa only [qmaThirdSeriesTarget,qmaSubdivisionTarget,mul_one] using
    qmaThirdTarget_norm H A B (fun _ => 1) J hH hA hB hc

omit [DecidableEq κ] in
theorem qmaScalarCoupling_sum (V : κ → Matrix σ σ ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ e, ‖spinMatrixOperator ((r:ℝ) • V e)‖) = r*∑ e, ‖spinMatrixOperator (V e)‖ := by
  simp only [qmaMatrix_real_smul_norm,abs_of_nonneg hr,Finset.mul_sum]

theorem qmaSpinMatrix_zero : spinMatrixOperator (0 : Matrix σ σ ℂ) = 0 := by
  ext x i
  simp

theorem qmaThirdWeight_neg (j : ℝ) : qmaThirdWeight (-j) = qmaThirdWeight j := by
  simp only [qmaThirdWeight,abs_neg]

end ContinuumCoulomb

end

end OAI
