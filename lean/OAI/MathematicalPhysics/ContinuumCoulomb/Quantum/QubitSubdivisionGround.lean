import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionScale
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitPhysicalComparison

namespace OAI

/-! Full-space error of the simultaneous subdivision gadget. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem qmaSubdivisionResidual_norm (L : Matrix σ σ ℂ) (P : κ → Matrix σ σ ℂ)
    {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hP : ∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ K) (hL : ‖spinMatrixOperator L‖ ≤ K) :
    ‖spinMatrixOperator (((R:ℂ)⁻¹)^2 • (∑ e, P e*L*P e))‖ ≤ K^2/R^2 := by
  calc
    _ ≤ R⁻¹^2*((∑ e, ‖spinMatrixOperator (P e)‖^2)*‖spinMatrixOperator L‖) :=
      qmaThirdResidual_norm L P R hR
    _ ≤ R⁻¹^2*(K*K) := mul_le_mul_of_nonneg_left
      (mul_le_mul hP hL (norm_nonneg _) hK) (sq_nonneg _)
    _ = _ := by field_simp

theorem qmaSubdivision_target_ground (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) {R K : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e)
    (hP : ∀ e, (qmaThirdSeriesPair (A e) (B e) (-J e)).conjTranspose =
      qmaThirdSeriesPair (A e) (B e) (-J e))
    (hLstar : (qmaSubdivisionLow H (fun e => J e)).conjTranspose =
      qmaSubdivisionLow H (fun e => J e))
    (hL : ‖spinMatrixOperator (qmaSubdivisionLow H (fun e => J e))‖ ≤ K)
    (hPsq : ∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (-J e))‖^2 ≤ K)
    (hTarget : ‖spinMatrixOperator (qmaSubdivisionTarget H A B (fun e => J e))‖ ≤ K)
    (hPert : ‖qmaPerturbationOperator (qmaSubdivisionLow H (fun e => J e)) (fun _ : κ => 0)
      (fun e => (R:ℝ) • qmaThirdSeriesPair (A e) (B e) (-J e))‖ ≤ K*R)
    (hCouple : ∑ e, ‖spinMatrixOperator ((R:ℝ) • qmaThirdSeriesPair (A e) (B e) (-J e))‖ ≤
      R^2*(K/R)) (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaSubdivisionGadget H A B R J)-
      MediatorGraph.normalizedBottom (qmaSubdivisionTarget H A B (fun e => J e))| ≤ 7*K^4/R := by
  let L := qmaSubdivisionLow H (fun e => J e)
  let P := fun e => qmaThirdSeriesPair (A e) (B e) (-J e)
  let V := fun e => (R:ℝ) • P e
  let M := qmaThirdMatrix L (fun _ : κ => 0) V (R^2:ℝ)
  let T := qmaSubdivisionTarget H A B (fun e => J e)
  let E := ((R:ℂ)⁻¹)^2 • (∑ e, P e*L*P e)
  have hRp : 0 < R := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR2 : K ≤ R^2 := by nlinarith
  have hident : M = T+E := qmaSubdivisionThirdMatrix_target H A B J R hRp.ne' hA hB hAB hP
  have hE : ‖spinMatrixOperator E‖ ≤ K^2/R^2 := qmaSubdivisionResidual_norm L P hRp hK0 hPsq hL
  have hsmallE : K^2/R^2 ≤ K := by
    apply (div_le_iff₀ (sq_pos_of_pos hRp)).mpr
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hR2 hK0
  have hM : ‖spinMatrixOperator M‖ ≤ 2*K := by
    rw [hident,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans ((add_le_add hTarget (hE.trans hsmallE)).trans_eq (by ring))
  have hError : ‖spinMatrixOperator (M-T)‖ ≤ K^2/R^2 := by
    simpa only [hident,add_sub_cancel_left] using hE
  have hVstar (e : κ) : (V e).conjTranspose = V e := by
    change ((R:ℝ) • P e).conjTranspose = (R:ℝ) • P e
    have hPe : (P e).conjTranspose = P e := hP e
    rw [Matrix.conjTranspose_smul,star_trivial,hPe]
  have he := qmaPhysical_target_error (R^2) L T (fun _ : κ => 0) V
    (sq_pos_of_pos hRp) hLstar (by intro e; simp) hVstar
    (show 0 ≤ K*R by positivity) (show 0 ≤ 2*K by positivity)
    (qmaSubdivision_scale_small hK hR) hPert hCouple hM hError u hu
  exact he.trans (qmaSubdivision_total_error hK hR)

end ContinuumCoulomb

end

end OAI
