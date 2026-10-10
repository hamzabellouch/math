import OAI.Analysis.HyperbolicCones.ResolventImaginary

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Paper256

theorem complex_resolvent_isSymm {n : ℕ} (X : Mat n ℝ) (hX : X.IsHermitian)
    (z : ℂ) : ((z • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹).IsSymm := by
  have hXt : Xᵀ = X := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hX.eq
  have hc : (X.map Complex.ofReal)ᵀ = X.map Complex.ofReal := by
    ext i j
    exact congrArg Complex.ofReal (congrFun (congrFun hXt i) j)
  change ((z • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹)ᵀ = _
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_sub, Matrix.transpose_smul, hc]

theorem resolvent_inverse_gram {n : ℕ} (X : Mat n ℝ) (hX : X.IsHermitian)
    (a η : ℝ) (hη : 0 < η) :
    (((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹)ᴴ *
      ((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹)) =
    (((a • (1 : Mat n ℝ) - X) ^ 2 + η ^ 2 • 1)⁻¹).map Complex.ofReal := by
  rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev,
    resolvent_mul_adjoint X hX a η]
  exact complexify_nonsing_inv _ (resolvent_denominator_posDef X hX a η hη).isUnit

theorem resolvent_imaginary_formula {n : ℕ} (X : Mat n ℝ) (hX : X.IsHermitian)
    (a η : ℝ) (hη : 0 < η) :
    (((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹).map
      Complex.im) = -(η : ℝ) • (((a • (1 : Mat n ℝ) - X) ^ 2 + η ^ 2 • 1)⁻¹) := by
  let z : ℂ := (a : ℂ) + (η : ℂ) * Complex.I
  let R := (z • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹
  have hz : z.im ≠ 0 := by simpa [z] using ne_of_gt hη
  have hd := resolvent_adjoint_difference (X.map Complex.ofReal)
    (isHermitian_complexify X hX) z
    ((Matrix.isUnit_iff_isUnit_det _).mp (complex_resolvent_isUnit X hX z hz))
  have hg := resolvent_inverse_gram X hX a η hη
  change Rᴴ * R = _ at hg
  change R - Rᴴ = -(z - star z) • (Rᴴ * R) at hd
  rw [hg] at hd
  have hs : R.IsSymm := complex_resolvent_isSymm X hX z
  ext i j
  have hsij : R j i = R i j := congrFun (congrFun hs i) j
  have hij := congrArg Complex.im (congrFun (congrFun hd i) j)
  simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.map_apply, hsij, Complex.sub_im, Complex.star_def,
    Complex.conj_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im] at hij
  change (R i j).im = -η * _
  simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
    zero_add, add_zero] at hij
  linarith

theorem resolvent_negative_imaginary_posDef {n : ℕ} (X : Mat n ℝ)
    (hX : X.IsHermitian) (a η : ℝ) (hη : 0 < η) :
    (-(((((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat n ℂ) - X.map Complex.ofReal)⁻¹).map
      Complex.im)).PosDef := by
  rw [resolvent_imaginary_formula X hX a η hη, neg_smul, neg_neg]
  exact (resolvent_denominator_posDef X hX a η hη).inv.smul hη

end Paper256

end

end OAI
