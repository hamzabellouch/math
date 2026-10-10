import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionNorm

namespace OAI

/-! One explicit coefficient budget discharges the subdivision norm bounds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaSubdivision_calibration (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {b R : ℝ} (hb : 0 ≤ b) (hR : 1 ≤ R)
    (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1) (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1) :
    let K := qmaThirdBudget b J
    let L := qmaSubdivisionLow H (fun e => J e)
    let P := fun e => qmaThirdSeriesPair (A e) (B e) (-J e)
    ‖spinMatrixOperator L‖ ≤ K ∧
      (∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ K) ∧
      ‖spinMatrixOperator (qmaSubdivisionTarget H A B (fun e => J e))‖ ≤ K ∧
      ‖qmaPerturbationOperator L (fun _ : κ => 0) (fun e => (R:ℝ) • P e)‖ ≤ K*R ∧
      (∑ e, ‖spinMatrixOperator ((R:ℝ) • P e)‖ ≤ R^2*(K/R)) := by
  let S := ∑ e, qmaThirdWeight (J e)
  let W := 1+b+S
  let L := qmaSubdivisionLow H (fun e => J e)
  let P := fun e => qmaThirdSeriesPair (A e) (B e) (-J e)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hSW : S ≤ W := by dsimp [W]; linarith
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hp0 := qmaThirdPair_sum_bounds A B (fun e => -J e) hA hB
  simp only [qmaThirdWeight_neg, Complex.ofReal_neg] at hp0
  have hpair : (∑ e, ‖spinMatrixOperator (P e)‖ ≤ S) ∧
      (∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ S) := by
    exact hp0
  have hL : ‖spinMatrixOperator L‖ ≤ W := by
    apply (qmaSubdivisionLow_norm H J hH).trans
    dsimp [W]
    linarith
  have hLbig : ‖spinMatrixOperator L‖ ≤ 4*W := hL.trans (by linarith)
  have hPsq : ∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ 4*W := hpair.2.trans (by linarith)
  have htarget : ‖spinMatrixOperator (qmaSubdivisionTarget H A B (fun e => J e))‖ ≤ 4*W := by
    apply (qmaSubdivisionTarget_norm H A B J hH hA hB).trans
    dsimp [W]
    linarith
  have hpert : ‖qmaPerturbationOperator L (fun _ : κ => 0) (fun e => (R:ℝ) • P e)‖ ≤ (4*W)*R := by
    have hn := qmaPerturbationOperator_norm L (fun _ : κ => 0) (fun e => (R:ℝ) • P e)
    simp only [qmaSpinMatrix_zero,norm_zero,Finset.sum_const_zero,add_zero,
      qmaScalarCoupling_sum P hR0] at hn
    have hp := mul_le_mul_of_nonneg_left (hpair.1.trans hSW) hR0
    have hrw : W ≤ R*W := by nlinarith
    nlinarith
  have hcouple : ∑ e, ‖spinMatrixOperator ((R:ℝ) • P e)‖ ≤ R^2*((4*W)/R) := by
    rw [qmaScalarCoupling_sum P hR0]
    calc
      _ ≤ R*(4*W) := mul_le_mul_of_nonneg_left (hpair.1.trans (by linarith)) hR0
      _ = _ := by field_simp
  exact ⟨hLbig,hPsq,htarget,hpert,hcouple⟩

end ContinuumCoulomb

end

end OAI
