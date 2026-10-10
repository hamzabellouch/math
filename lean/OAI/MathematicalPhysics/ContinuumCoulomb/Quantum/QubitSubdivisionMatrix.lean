import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdGadget

namespace OAI

/-! The simultaneous subdivision gadget has only a scalar counterterm.
Its exact third-order compression retains the common low-block residual. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaSubdivisionLow (H : Matrix σ σ ℂ) (J : κ → ℂ) : Matrix σ σ ℂ :=
  H+∑ e, qmaSubdivisionCounter (J e)

def qmaSubdivisionTarget (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) : Matrix σ σ ℂ := H+∑ e, J e • (A e*B e)

def qmaSubdivisionGadget (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (R : ℝ) (J : κ → ℝ) : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  qmaPhysicalMediatorMatrix (R^2) (qmaSubdivisionLow H (fun e => J e)) (fun _ => 0)
    (fun e => (R:ℝ) • qmaThirdSeriesPair (A e) (B e) (-J e))

theorem qmaSubdivision_pair_effective (A B : Matrix σ σ ℂ) (J : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A) :
    qmaSubdivisionCounter J-
      qmaThirdSeriesPair A B (-J)*qmaThirdSeriesPair A B (-J) = J • (A*B) := by
  unfold qmaSubdivisionCounter qmaThirdSeriesPair
  rw [qmaGadget_pair_square A B (-J/2) hA hB hAB]
  module

omit [DecidableEq κ] in
theorem qmaSubdivision_sum_effective (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) :
    qmaSubdivisionLow H J-
      (∑ e, qmaThirdSeriesPair (A e) (B e) (-J e)*qmaThirdSeriesPair (A e) (B e) (-J e)) =
        qmaSubdivisionTarget H A B J := by
  calc
    _ = H+∑ e, (qmaSubdivisionCounter (J e)-
        qmaThirdSeriesPair (A e) (B e) (-J e)*qmaThirdSeriesPair (A e) (B e) (-J e)) := by
      simp only [qmaSubdivisionLow,Finset.sum_sub_distrib]
      abel
    _ = _ := by
      unfold qmaSubdivisionTarget
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      exact qmaSubdivision_pair_effective (A e) (B e) (J e) (hA e) (hB e) (hAB e)

omit [DecidableEq κ] in
theorem qmaSubdivisionThirdMatrix_scaled (L : Matrix σ σ ℂ) (P : κ → Matrix σ σ ℂ)
    (R : ℝ) (hR : R ≠ 0) (hP : ∀ e, (P e).conjTranspose = P e) :
    qmaThirdMatrix L (fun _ : κ => 0) (fun e => (R:ℝ) • P e) (R^2:ℝ) =
      L-(∑ e, P e*P e)+((R:ℂ)⁻¹)^2 • (∑ e, P e*L*P e) := by
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have hfirst : ((R:ℂ)^2)⁻¹*((R:ℂ)*(R:ℂ)) = 1 := by field_simp
  have hremain : (((R:ℂ)^2)⁻¹)^2*((R:ℂ)*(R:ℂ)) = ((R:ℂ)⁻¹)^2 := by field_simp
  have hs (r : ℝ) (M : Matrix σ σ ℂ) : r • M = (r:ℂ) • M := rfl
  unfold qmaThirdMatrix
  simp only [hs,Complex.ofReal_pow,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
    hP,smul_mul_assoc,mul_smul_comm,smul_smul,← Finset.smul_sum,
    mul_zero,zero_mul,Finset.sum_const_zero,smul_zero,add_zero,hfirst,hremain,one_smul]

omit [DecidableEq κ] in
theorem qmaSubdivisionThirdMatrix_target (H : Matrix σ σ ℂ) (A B : κ → Matrix σ σ ℂ)
    (J : κ → ℝ) (R : ℝ) (hR : R ≠ 0)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e)
    (hP : ∀ e, (qmaThirdSeriesPair (A e) (B e) (-J e)).conjTranspose =
      qmaThirdSeriesPair (A e) (B e) (-J e)) :
    let L := qmaSubdivisionLow H (fun e => J e)
    let P := fun e => qmaThirdSeriesPair (A e) (B e) (-J e)
    qmaThirdMatrix L (fun _ : κ => 0) (fun e => (R:ℝ) • P e) (R^2:ℝ) =
      qmaSubdivisionTarget H A B (fun e => J e)+((R:ℂ)⁻¹)^2 • (∑ e, P e*L*P e) := by
  dsimp only
  rw [qmaSubdivisionThirdMatrix_scaled _ _ R hR hP,
    qmaSubdivision_sum_effective H A B (fun e => J e) hA hB hAB]

end ContinuumCoulomb

end

end OAI
