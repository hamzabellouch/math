import OAI.Analysis.HyperbolicCones.MatrixResolvent

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Paper256

theorem complex_symmetric_imaginary {n : ℕ} (A : Mat n ℂ) (hA : A.IsSymm) :
    (A.map Complex.im).map Complex.ofReal = (2 * Complex.I)⁻¹ • (A - Aᴴ) := by
  ext i j
  have h := congrFun (congrFun hA i) j
  change A j i = A i j at h
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, Matrix.conjTranspose_apply, h]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.inv_re,
    Complex.inv_im, Complex.normSq]
  ring

theorem complex_symmetric_imaginary_isSymm {n : ℕ} (A : Mat n ℂ) (hA : A.IsSymm) :
    (A.map Complex.im).IsSymm := by
  ext i j
  exact congrArg Complex.im (congrFun (congrFun hA i) j)

theorem complexify_nonsing_inv {n : ℕ} (A : Mat n ℝ) (hA : IsUnit A) :
    (A.map Complex.ofReal)⁻¹ = A⁻¹.map Complex.ofReal := by
  apply Matrix.inv_eq_right_inv
  have hf : (Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal := by
    funext x
    rfl
  have h := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have ho : (1 : Mat n ℝ).map Complex.ofRealHom = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]
  have hc := congrArg (fun M : Mat n ℝ => M.map Complex.ofRealHom) h
  rw [Matrix.map_mul, ho] at hc
  simpa only [hf] using hc

theorem resolvent_denominator_posDef {n : ℕ} (X : Mat n ℝ) (hX : X.IsHermitian)
    (a η : ℝ) (hη : 0 < η) :
    ((a • (1 : Mat n ℝ) - X) ^ 2 + η ^ 2 • 1).PosDef := by
  have hR : (a • (1 : Mat n ℝ) - X).IsHermitian :=
    ((Matrix.isHermitian_one).smul (IsSelfAdjoint.all a)).sub hX
  have hsq : ((a • (1 : Mat n ℝ) - X) ^ 2).PosSemidef := by
    simpa only [pow_two, hR.eq] using
      Matrix.posSemidef_conjTranspose_mul_self (a • (1 : Mat n ℝ) - X)
  exact Matrix.PosDef.posSemidef_add hsq (Matrix.PosDef.one.smul (sq_pos_of_pos hη))

theorem resolvent_mul_adjoint {n : ℕ} (X : Mat n ℝ) (hX : X.IsHermitian)
    (a η : ℝ) :
    (((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat n ℂ) - X.map Complex.ofReal) *
      (((a : ℂ) + (η : ℂ) * Complex.I) • (1 : Mat n ℂ) - X.map Complex.ofReal)ᴴ =
    (((a • (1 : Mat n ℝ) - X) ^ 2 + η ^ 2 • 1).map Complex.ofReal) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    (isHermitian_complexify X hX).eq]
  have hf : (Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal := by
    funext x
    rfl
  have hm : ((a • (1 : Mat n ℝ) - X) ^ 2).map Complex.ofReal =
      ((a • (1 : Mat n ℝ) - X).map Complex.ofReal) *
      ((a • (1 : Mat n ℝ) - X).map Complex.ofReal) := by
    simpa only [pow_two, hf] using (Matrix.map_mul (f := Complex.ofRealHom)
      (L := a • (1 : Mat n ℝ) - X) (M := a • (1 : Mat n ℝ) - X))
  have hr : (a • (1 : Mat n ℝ) - X).map Complex.ofReal =
      (a : ℂ) • 1 - X.map Complex.ofReal := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hij]
  have hb : (((a • (1 : Mat n ℝ) - X) ^ 2 + η ^ 2 • 1).map Complex.ofReal) =
      (((a • (1 : Mat n ℝ) - X) ^ 2).map Complex.ofReal) + (η : ℂ)^2 • 1 := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hij]
  rw [hb, hm, hr]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [map_add, map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp

end Paper256

end

end OAI
