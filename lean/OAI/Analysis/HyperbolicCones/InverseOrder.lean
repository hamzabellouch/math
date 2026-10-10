import OAI.Analysis.HyperbolicCones.KernelSpectrum

namespace OAI

/-! Simultaneous spectral comparison of a positive matrix and its scalar shifts. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem matrix_cfc_affine {n : ℕ} (H : Sym n) (a b : ℝ) :
    cfc (fun x : ℝ => a + b * x) (H : Mat n ℝ) =
      a • (1 : Mat n ℝ) + b • (H : Mat n ℝ) := by
  calc
    _ = algebraMap ℝ (Mat n ℝ) a + cfc (fun x : ℝ => b * x) (H : Mat n ℝ) :=
      cfc_const_add a (fun x : ℝ => b * x) (H : Mat n ℝ)
        (H.val.finite_real_spectrum.continuousOn _) H.property
    _ = _ := by
      have hmul : cfc (fun x : ℝ => b * x) (H : Mat n ℝ) = b • (H : Mat n ℝ) :=
        cfc_const_mul_id b (H : Mat n ℝ) H.property
      rw [hmul, Algebra.algebraMap_eq_smul_one]

theorem posDef_inverse_eq_cfc {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    (H : Mat n ℝ)⁻¹ = cfc (fun x : ℝ => x⁻¹) (H : Mat n ℝ) := by
  have hi := cfc_inv (fun x : ℝ => x) (H : Mat n ℝ)
    (fun x hx => (posDef_real_spectrum_positive hH hx).ne')
    (H.val.finite_real_spectrum.continuousOn _) H.property
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  rw [hid, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  exact hi.symm

theorem posDef_shift_inverse_eq_cfc {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((H : Mat n ℝ) + t • 1)⁻¹ =
      cfc (fun x : ℝ => (x + t)⁻¹) (H : Mat n ℝ) := by
  have hi := cfc_inv (fun x : ℝ => x + t) (H : Mat n ℝ)
    (fun x hx => (add_pos_of_pos_of_nonneg (posDef_real_spectrum_positive hH hx) ht).ne')
    (H.val.finite_real_spectrum.continuousOn _) H.property
  have hshift : cfc (fun x : ℝ => x + t) (H : Mat n ℝ) =
      (H : Mat n ℝ) + t • 1 := by
    simpa only [add_comm, one_mul, one_smul] using matrix_cfc_affine H t 1
  rw [hshift, ← Matrix.nonsing_inv_eq_ringInverse] at hi
  exact hi.symm

theorem posDef_inverse_sub_shift_inverse_posSemidef {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((H : Mat n ℝ)⁻¹ - ((H : Mat n ℝ) + t • 1)⁻¹).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg, posDef_inverse_eq_cfc H hH, posDef_shift_inverse_eq_cfc H hH t ht]
  apply cfc_mono _ (H.val.finite_real_spectrum.continuousOn _)
    (H.val.finite_real_spectrum.continuousOn _)
  intro x hx
  exact inv_anti₀ (posDef_real_spectrum_positive hH hx) (le_add_of_nonneg_right ht)

end Paper256

end

end OAI
