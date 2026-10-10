import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCertificateRecipe
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardMatching

namespace OAI

/-! The rational profile product is the actual normalized backward matrix. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

noncomputable def complexMatrix (A : QMatrix) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix2.toMatrix A).map RationalComplex.toComplex

@[simp] theorem complexMatrix_one : complexMatrix Matrix2.one = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexMatrix, Matrix2.one, Matrix2.toMatrix]

@[simp] theorem complexMatrix_mul (A B : QMatrix) :
    complexMatrix (Matrix2.mul A B) = complexMatrix A * complexMatrix B := by
  simp only [complexMatrix, Matrix2.toMatrix_mul, Matrix.map_mul]

@[simp] theorem complexMatrix_scale (r : RationalComplex) (A : QMatrix) :
    complexMatrix (Matrix2.scale r A) = RationalComplex.toComplex r • complexMatrix A := by
  simp only [complexMatrix, Matrix2.toMatrix_scale]
  exact Matrix.map_smul' _ _ _ RationalComplex.toComplex.map_mul

/-- Each factor in the finite product, including its manuscript normalization. -/
noncomputable def profileFactor (b Z : ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((n : ℂ)+1)⁻¹ • backwardMatrix 5 (Complex.I * Z) ((n : ℂ)-Complex.I*b)

noncomputable def profileProduct (b Z : ℝ) (K : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((K.factorial : ℂ)⁻¹) • backwardProduct 5 (Complex.I * Z) (-Complex.I*b) K

private theorem factor_complex (n : ℕ) :
    complexMatrix (factor n) =
      backwardMatrix 5 (Complex.I * (centerZ : ℝ)) ((n : ℂ)-Complex.I*(centerB : ℝ)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [complexMatrix, factor, Matrix2.toMatrix, backwardMatrix,
      RationalComplex.toComplex, Complex.ext_iff]

private theorem inverse_complex (n : ℕ) :
    RationalComplex.toComplex (⟨((n : ℚ)+1)⁻¹,0⟩ : RationalComplex) = ((n : ℂ)+1)⁻¹ := by
  have hr (r : ℚ) : RationalComplex.toComplex (⟨r,0⟩ : RationalComplex) = (r : ℂ) := by
    apply Complex.ext <;> simp [RationalComplex.toComplex]
  simpa using hr (((n : ℚ)+1)⁻¹)

theorem complexMatrix_step (n : ℕ) (s : State) :
    complexMatrix (step n s).value =
      profileFactor (centerB : ℝ) (centerZ : ℝ) n * complexMatrix s.value := by
  simp only [step, complexMatrix_scale, complexMatrix_mul, factor_complex, inverse_complex,
    profileFactor, Matrix.smul_mul]

theorem complexMatrix_foldr (ns : List ℕ) :
    complexMatrix (ns.foldr step initial).value =
      (ns.map (profileFactor (centerB : ℝ) (centerZ : ℝ))).prod := by
  induction ns with
  | nil => simp [initial]
  | cons n ns ih => simp only [List.foldr_cons, complexMatrix_step, ih, List.map_cons, List.prod_cons]

theorem profileFactor_product (b Z : ℝ) (K : ℕ) :
    ((List.range K).map (profileFactor b Z)).prod = profileProduct b Z K := by
  induction K with
  | zero => simp [profileProduct, backwardProduct]
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, ih]
    simp only [profileProduct, profileFactor, backwardProduct, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    have he : (-Complex.I * (b : ℂ)) + K = (K : ℂ) - Complex.I*b := by ring
    rw [he]
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, _root_.mul_inv_rev]
    ring

theorem result_value_eq_profileProduct :
    complexMatrix result.value = profileProduct (centerB : ℝ) (centerZ : ℝ) 34 := by
  rw [result, complexMatrix_foldr, profileFactor_product]

end DefocusingNLS.ProfileCertificate

end OAI
