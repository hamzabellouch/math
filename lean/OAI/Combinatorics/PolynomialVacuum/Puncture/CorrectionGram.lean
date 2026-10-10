import OAI.Combinatorics.PolynomialVacuum.Puncture.ScalarJensen

namespace OAI

namespace PolynomialVacuumCylinder
open MeasureTheory Matrix

theorem denominator_correction_gram_identity {n : ℕ} (u : Fin n → ℝ) :
    star u ⬝ᵥ ((denominatorCorrectionMatrix n)*ᵥ u) =
      ∫ p : ℝ,(evenMomentEvaluation u p)^2*denominatorReferenceWeight p*denominatorCorrection p := by
  have hex p : (evenMomentEvaluation u p)^2*denominatorReferenceWeight p*denominatorCorrection p =
      ∑ j,∑ k,(u j*u k)*(p^(2*j.val+2*k.val)*denominatorReferenceWeight p*denominatorCorrection p) := by
    unfold evenMomentEvaluation
    rw [pow_two,Finset.sum_mul,Finset.sum_mul]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_add]
    ring
  simp_rw [hex]
  rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>
    (denominatorCorrectionMatrix_entry_integrable n j k).const_mul (u j*u k)))]
  simp_rw [integral_finsetSum _ (fun k _=>
    (denominatorCorrectionMatrix_entry_integrable n _ k).const_mul (_*u k)),integral_const_mul]
  simp only [dotProduct,mulVec,Pi.star_apply,star_trivial,denominatorCorrectionMatrix]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem conjugate_diagonal_gram {n : ℕ} (G V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (star V*G*V) i i = star (V.col i) ⬝ᵥ (G*ᵥ V.col i) := by
  simp only [star_eq_conjTranspose,mul_apply,conjTranspose_apply,star_trivial,
    dotProduct,mulVec,Pi.star_apply,Matrix.col,Matrix.transpose_apply]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem isUnit_col_ne_zero {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : IsUnit V) (i : Fin n) : V.col i≠0 := by
  intro hz
  have he : V*ᵥ Pi.single i 1=V*ᵥ 0 := by simpa using hz
  have h := congrFun (Matrix.mulVec_injective_iff_isUnit.mpr hV he) i
  simp at h

end PolynomialVacuumCylinder

end OAI
