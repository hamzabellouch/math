import OAI.Analysis.HyperbolicCones.FormBasic

namespace OAI

/-! Positivity of the Choi--Lam form, including its principal-minor argument. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem cyclic_cubic_nonnegative (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3 * a * b * c := by
  have aux (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
      0 ≤ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 3 * a * b * c := by
    have h := add_nonneg
      (mul_nonneg hc (add_nonneg (sq_nonneg (a - b))
        (mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb))))
      (mul_nonneg (sq_nonneg (a - c)) (sub_nonneg.mpr hcb))
    nlinarith only [h]
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · nlinarith only [aux b c a ha hab hac]
    · exact aux a b c hc hca (hca.trans hab)
  · rcases le_total b c with hbc | hcb
    · nlinarith only [aux c a b hb hbc hba]
    · exact aux a b c hc (hcb.trans hba) hcb

theorem zMatrix_det_nonnegative (z : Fin 3 → ℝ) : 0 ≤ Matrix.det (zMatrix z) := by
  rw [zMatrix_det]
  exact cyclic_cubic_nonnegative _ _ _ (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)

private theorem quadratic_two_nonnegative (a b c x y : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : b ^ 2 ≤ a * c) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    simpa [ha0, hb0] using mul_nonneg hc (sq_nonneg y)
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h := add_nonneg (sq_nonneg (a * x + b * y))
      (mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg y))
    have hm : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
      nlinarith only [h]
    exact nonneg_of_mul_nonneg_right hm hapos

private theorem quadratic_three_nonnegative (a b c d e f x y z : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hab : b ^ 2 ≤ a * d) (hac : c ^ 2 ≤ a * f) (hdf : e ^ 2 ≤ d * f)
    (hdet : 0 ≤ a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d) :
    0 ≤ a * x ^ 2 + d * y ^ 2 + f * z ^ 2 +
      2 * b * x * y + 2 * c * x * z + 2 * e * y * z := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    have hc0 : c = 0 := by nlinarith [sq_nonneg c]
    have h := quadratic_two_nonnegative d e f y z hd hf hdf
    simpa [ha0, hb0, hc0, add_comm, add_left_comm, add_assoc] using h
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hsmall : (a * e - b * c) ^ 2 ≤ (a * d - b ^ 2) * (a * f - c ^ 2) := by
      nlinarith only [mul_nonneg ha hdet]
    have hs := quadratic_two_nonnegative (a * d - b ^ 2) (a * e - b * c)
      (a * f - c ^ 2) y z (sub_nonneg.mpr hab) (sub_nonneg.mpr hac) hsmall
    have hm : 0 ≤ a * (a * x ^ 2 + d * y ^ 2 + f * z ^ 2 +
        2 * b * x * y + 2 * c * x * z + 2 * e * y * z) := by
      nlinarith only [sq_nonneg (a * x + b * y + c * z), hs]
    exact nonneg_of_mul_nonneg_right hm hapos

/-- For a symmetric three-by-three matrix, its principal minors certify positivity. -/
theorem posSemidef_three_of_principal_minors (M : Mat 3 ℝ) (hM : M.IsHermitian)
    (hdiag : ∀ i, 0 ≤ M i i)
    (h01 : M 0 1 ^ 2 ≤ M 0 0 * M 1 1)
    (h02 : M 0 2 ^ 2 ≤ M 0 0 * M 2 2)
    (h12 : M 1 2 ^ 2 ≤ M 1 1 * M 2 2) (hdet : 0 ≤ Matrix.det M) :
    M.PosSemidef := by
  have h10 : M 1 0 = M 0 1 := by simpa using hM.apply 0 1
  have h20 : M 2 0 = M 0 2 := by simpa using hM.apply 0 2
  have h21 : M 2 1 = M 1 2 := by simpa using hM.apply 1 2
  have hd : 0 ≤ M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 ^ 2 -
      M 0 1 ^ 2 * M 2 2 + 2 * M 0 1 * M 0 2 * M 1 2 - M 0 2 ^ 2 * M 1 1 := by
    rw [Matrix.det_fin_three, h10, h20, h21] at hdet
    nlinarith only [hdet]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => ?_
  have h := quadratic_three_nonnegative (M 0 0) (M 0 1) (M 0 2)
    (M 1 1) (M 1 2) (M 2 2) (x 0) (x 1) (x 2)
    (hdiag 0) (hdiag 1) (hdiag 2) h01 h02 h12 hd
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10, h20, h21]
  nlinarith only [h]

theorem zMatrix_posSemidef (z : Fin 3 → ℝ) : (zMatrix z).PosSemidef := by
  apply posSemidef_three_of_principal_minors _ (zMatrix_isHermitian z)
    (zMatrix_diag_nonnegative z)
  · have h := zMatrix_principal_minor_two_nonnegative z 0
    simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix, Fin.reduceAdd] at h ⊢
    nlinarith only [h]
  · have h := zMatrix_principal_minor_two_nonnegative z 2
    simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix, Fin.reduceAdd, Fin.reduceEq] at h ⊢
    nlinarith only [h]
  · have h := zMatrix_principal_minor_two_nonnegative z 1
    simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix, Fin.reduceAdd, Fin.reduceEq] at h ⊢
    nlinarith only [h]
  · exact zMatrix_det_nonnegative z

theorem choiLam_nonnegative (z y : Fin 3 → ℝ) : 0 ≤ choiLam z y := by
  have h := (zMatrix_posSemidef z).dotProduct_mulVec_nonneg y
  simpa only [star_trivial, zMatrix_quadratic] using h

theorem qMatrix_posSemidef (y : Fin 3 → ℝ) : (qMatrix y).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (qMatrix_isHermitian y) fun z => ?_
  simpa only [star_trivial, qMatrix_quadratic] using choiLam_nonnegative z y

end Paper256

end

end OAI
