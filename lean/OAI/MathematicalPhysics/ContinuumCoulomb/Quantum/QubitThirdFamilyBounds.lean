import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdNormBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorSeriesMatrix

namespace OAI

/-! Summed polynomial coefficient bounds for an actual parallel gadget family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaThirdBudget (b : ℝ) (J : κ → ℝ) : ℝ := 4*(1+b+∑ e, qmaThirdWeight (J e))

theorem qmaThirdWeight_pair (j : ℝ) : 1+|j| ≤ qmaThirdWeight j := by
  have hj := abs_nonneg j
  dsimp [qmaThirdWeight]
  nlinarith

omit [DecidableEq κ] in
theorem qmaThirdBudget_pos {b : ℝ} (hb : 0 ≤ b) (J : κ → ℝ) : 1 ≤ qmaThirdBudget b J := by
  have hs : 0 ≤ ∑ e, qmaThirdWeight (J e) := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  unfold qmaThirdBudget
  linarith

omit [DecidableEq κ] in
theorem qmaThirdPair_sum_bounds (A B : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1) :
    (∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (J e))‖ ≤
        ∑ e, qmaThirdWeight (J e)) ∧
      (∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (J e))‖^2 ≤
        ∑ e, qmaThirdWeight (J e)) := by
  constructor
  · exact Finset.sum_le_sum (fun e _ =>
      (qmaThirdPair_norm (A e) (B e) (J e) (hA e) (hB e)).trans (qmaThirdWeight_pair (J e)))
  · apply Finset.sum_le_sum
    intro e _
    exact pow_le_pow_left₀ (norm_nonneg _) (qmaThirdPair_norm (A e) (B e) (J e) (hA e) (hB e)) 2

omit [DecidableEq κ] in
theorem qmaThirdLow_norm (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    {r b : ℝ} (hr : 0 ≤ r) (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1)
    (hC : ∀ e, ‖spinMatrixOperator (C e)‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesLow H A B C r (fun e => J e))‖ ≤
      b+(r+1)*(∑ e, qmaThirdWeight (J e)) := by
  unfold qmaThirdSeriesLow
  rw [spinMatrixOperator_add,spinMatrixOperator_sum]
  calc
    _ ≤ ‖spinMatrixOperator H‖+∑ e, ‖spinMatrixOperator
        (qmaThirdSeriesCounter (A e) (B e) (C e) r (J e))‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ b+∑ e, (r+1)*qmaThirdWeight (J e) := add_le_add hH
      (Finset.sum_le_sum (fun e _ => qmaThirdCounter_norm _ _ _ r (J e) hr (hA e) (hB e) (hC e)))
    _ = _ := by rw [Finset.mul_sum]

omit [DecidableEq κ] in
theorem qmaThirdTarget_norm (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ) (J : κ → ℝ)
    {b : ℝ} (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1)
    (hC : ∀ e, ‖spinMatrixOperator (C e)‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C (fun e => J e))‖ ≤
      b+∑ e, qmaThirdWeight (J e) := by
  unfold qmaThirdSeriesTarget
  rw [spinMatrixOperator_add,spinMatrixOperator_sum]
  apply (norm_add_le _ _).trans
  apply add_le_add hH
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hp := qmaMatrix_product_norm (A e*B e) (C e)
    (qmaMatrix_product_norm (A e) (B e) (hA e) (hB e)) (hC e)
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans
    (by simpa only [mul_one] using (qmaThirdWeight_bounds (J e)).2.1)

omit [DecidableEq κ] in
theorem qmaScaledCoupling_sum (V : κ → Matrix σ σ ℂ) (r : ℝ) :
    (∑ e, ‖spinMatrixOperator ((r^2:ℝ) • V e)‖) = r^2*∑ e, ‖spinMatrixOperator (V e)‖ := by
  simp only [qmaMatrix_real_smul_norm,abs_of_nonneg (sq_nonneg r),Finset.mul_sum]

theorem qmaScaledPerturbation_norm (L : Matrix σ σ ℂ) (C P : κ → Matrix σ σ ℂ)
    {r w : ℝ} (hr : 1 ≤ r) (hw : 0 ≤ w)
    (hL : ‖spinMatrixOperator L‖ ≤ 2*w*r)
    (hC : ∑ e, ‖spinMatrixOperator (C e)‖ ≤ w)
    (hP : ∑ e, ‖spinMatrixOperator (P e)‖ ≤ w) :
    ‖qmaPerturbationOperator L (fun e => (r^2:ℝ) • C e)
      (fun e => (r^2:ℝ) • P e)‖ ≤ (4*w)*r^2 := by
  have hn := qmaPerturbationOperator_norm L (fun e => (r^2:ℝ) • C e)
    (fun e => (r^2:ℝ) • P e)
  rw [qmaScaledCoupling_sum,qmaScaledCoupling_sum] at hn
  have hc := mul_le_mul_of_nonneg_left hC (sq_nonneg r)
  have hp := mul_le_mul_of_nonneg_left hP (sq_nonneg r)
  have hr2 : r ≤ r^2 := by nlinarith
  have hwr := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ 2*w by positivity)
  nlinarith

end ContinuumCoulomb

end

end OAI
