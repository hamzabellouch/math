import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileTaylorStep

namespace OAI

/-! Interpretation of every field in the exact profile-certificate recurrence. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

@[simp] theorem complexMatrix_add (A B : QMatrix) :
    complexMatrix (Matrix2.add A B) = complexMatrix A+complexMatrix B := by
  ext i j
  simp only [complexMatrix, Matrix2.toMatrix_add, Matrix.map_apply, Matrix.add_apply, map_add]

@[simp] theorem rationalMatrix_add (E F : RMatrix) :
    rationalMatrix (Matrix2.add E F) = rationalMatrix E+rationalMatrix F := by
  ext i j
  simp only [rationalMatrix, Matrix2.toMatrix_add, Matrix.map_apply, Matrix.add_apply, map_add]

@[simp] theorem rationalMatrix_mul (E F : RMatrix) :
    rationalMatrix (Matrix2.mul E F) = rationalMatrix E*rationalMatrix F := by
  simp only [rationalMatrix, Matrix2.toMatrix_mul, Matrix.map_mul]

@[simp] theorem rationalMatrix_scale (r : ℚ) (E : RMatrix) :
    rationalMatrix (Matrix2.scale r E) = (r : ℝ) • rationalMatrix E := by
  simp only [rationalMatrix, Matrix2.toMatrix_scale]
  exact Matrix.map_smul' _ _ _ (Rat.castHom ℝ).map_mul

@[simp] theorem complexMatrix_scale_real (r : ℚ) (A : QMatrix) :
    complexMatrix (Matrix2.scale (⟨r,0⟩ : RationalComplex) A) = (r : ℝ) • complexMatrix A := by
  rw [complexMatrix_scale]
  have he : RationalComplex.toComplex (⟨r,0⟩ : RationalComplex) = ((r : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [RationalComplex.toComplex]
  rw [he]
  ext i j
  exact (Complex.real_smul).symm

theorem state_value_step (n : ℕ) (s : State) :
    complexMatrix (step n s).value = ((n : ℝ)+1)⁻¹ •
      (complexMatrix (factor n)*complexMatrix s.value) := by
  simp only [step, complexMatrix_scale_real, complexMatrix_mul]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem state_derivB_step (n : ℕ) (s : State) :
    complexMatrix (step n s).derivB = ((n : ℝ)+1)⁻¹ •
      (complexMatrix parameterB*complexMatrix s.value+
        complexMatrix (factor n)*complexMatrix s.derivB) := by
  simp only [step, complexMatrix_scale_real, complexMatrix_add, complexMatrix_mul]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem state_derivZ_step (n : ℕ) (s : State) :
    complexMatrix (step n s).derivZ = ((n : ℝ)+1)⁻¹ •
      (complexMatrix parameterZ*complexMatrix s.value+
        complexMatrix (factor n)*complexMatrix s.derivZ) := by
  simp only [step, complexMatrix_scale_real, complexMatrix_add, complexMatrix_mul]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem state_error_step (n : ℕ) (s : State) :
    rationalMatrix (step n s).error = ((n : ℝ)+1)⁻¹ •
      ((absoluteMatrix (factor n)+(radius : ℝ) •
          (absoluteMatrix parameterB+absoluteMatrix parameterZ))*rationalMatrix s.error+
        (absoluteMatrix parameterB+absoluteMatrix parameterZ)*
          (absoluteMatrix s.derivB+absoluteMatrix s.derivZ)) := by
  simp only [step, rationalMatrix_scale, rationalMatrix_add, rationalMatrix_mul,
    majorant, absoluteMatrix]
  simp only [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem profileFactor_affine (n : ℕ) (b z : ℝ) :
    profileFactor ((centerB : ℝ)+b) ((centerZ : ℝ)+z) n = ((n : ℝ)+1)⁻¹ •
      (complexMatrix (factor n)+b • complexMatrix parameterB+z • complexMatrix parameterZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [profileFactor, complexMatrix, factor, parameterB, parameterZ,
      Matrix2.toMatrix, backwardMatrix, RationalComplex.toComplex, Complex.real_smul,
      Complex.ext_iff] <;> ring

end DefocusingNLS.ProfileCertificate

end OAI
