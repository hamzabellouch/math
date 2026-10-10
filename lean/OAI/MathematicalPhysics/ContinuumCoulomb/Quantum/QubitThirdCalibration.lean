import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdFamilyBounds

namespace OAI

/-! All norm hypotheses of the physical third-order comparison follow from
one explicit polynomial in the original real coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdFamily_calibration (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {b R : ℝ} (hb : 0 ≤ b) (hR : 1 ≤ R)
    (hH : ‖spinMatrixOperator H‖ ≤ b)
    (hA : ∀ e, ‖spinMatrixOperator (A e)‖ ≤ 1)
    (hB : ∀ e, ‖spinMatrixOperator (B e)‖ ≤ 1)
    (hC : ∀ e, ‖spinMatrixOperator (C e)‖ ≤ 1) :
    let K := qmaThirdBudget b J
    let L := qmaThirdSeriesLow H A B C R (fun e => J e)
    let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
    ‖spinMatrixOperator L‖ ≤ K*R ∧
      (∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ K) ∧
      ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C (fun e => J e))‖ ≤ K ∧
      ‖qmaPerturbationOperator L (fun e => (R^2:ℝ) • C e)
        (fun e => (R^2:ℝ) • P e)‖ ≤ K*R^2 ∧
      (∑ e, ‖spinMatrixOperator ((R^2:ℝ) • P e)‖ ≤ R^3*(K/R)) := by
  let S := ∑ e, qmaThirdWeight (J e)
  let W := 1+b+S
  let L := qmaThirdSeriesLow H A B C R (fun e => J e)
  let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hSW : S ≤ W := by dsimp [W]; linarith
  have hW : 0 ≤ W := by dsimp [W]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hRp : 0 < R := by linarith
  have hpair := qmaThirdPair_sum_bounds A B J hA hB
  have hnormL : ‖spinMatrixOperator L‖ ≤ b+(R+1)*S := qmaThirdLow_norm H A B C J hR0 hH hA hB hC
  have hL : ‖spinMatrixOperator L‖ ≤ 2*W*R := by
    apply hnormL.trans
    have hbr : b ≤ b*R := by nlinarith
    have hsr : S ≤ S*R := by nlinarith
    dsimp [W]
    nlinarith
  have hsumC : ∑ e, ‖spinMatrixOperator (C e)‖ ≤ W := by
    apply le_trans (Finset.sum_le_sum (fun e _ => (hC e).trans (qmaThirdWeight_bounds (J e)).1))
    exact hSW
  have hsumP : ∑ e, ‖spinMatrixOperator (P e)‖ ≤ W := hpair.1.trans hSW
  have hLbig : ‖spinMatrixOperator L‖ ≤ (4*W)*R := by
    apply hL.trans
    nlinarith
  have hPsq : ∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ 4*W := by
    apply hpair.2.trans
    nlinarith
  have htarget : ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C (fun e => J e))‖ ≤ 4*W := by
    apply (qmaThirdTarget_norm H A B C J hH hA hB hC).trans
    dsimp [W]
    linarith
  have hpert := qmaScaledPerturbation_norm L C P hR hW hL hsumC hsumP
  have hcouple : ∑ e, ‖spinMatrixOperator ((R^2:ℝ) • P e)‖ ≤ R^3*((4*W)/R) := by
    rw [qmaScaledCoupling_sum]
    calc
      _ ≤ R^2*W := mul_le_mul_of_nonneg_left hsumP (sq_nonneg R)
      _ ≤ R^2*(4*W) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg R)
      _ = _ := by field_simp
  exact ⟨hLbig,hPsq,htarget,hpert,hcouple⟩

end ContinuumCoulomb

end

end OAI
