import OAI.Analysis.GroupDeterminants.RegularOperators

namespace OAI

universe uF uR ur um

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ProjectionScalars
variable {F : Type uF} {R : Type uR} [Field F] [Ring R] [Algebra F R]

def projectionReweight (P : R) (a b : F) : R := a • P + b • (1 - P)

theorem projectionReweight_mul (P : R) (hP : P * P = P) (a b c d : F) :
    projectionReweight P a b * projectionReweight P c d =
      projectionReweight P (a * c) (b * d) := by
  have h₁ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have h₂ : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have h₃ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  simp only [projectionReweight, add_mul, mul_add, smul_mul_smul_comm, hP,
    h₁, h₂, h₃, smul_zero, add_zero, zero_add]

@[simp] theorem projectionReweight_one (P : R) : projectionReweight P (1 : F) 1 = 1 := by
  simp [projectionReweight]

def projectionReweightUnit (P : R) (hP : P * P = P) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Rˣ where
  val := projectionReweight P a b
  inv := projectionReweight P a⁻¹ b⁻¹
  val_inv := by rw [projectionReweight_mul P hP]; simp [ha, hb]
  inv_val := by rw [projectionReweight_mul P hP]; simp [ha, hb]

end ProjectionScalars

section ShearAlgebra
variable {R : Type uR} {r : Type ur} {m : Type um} [Ring R] [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

def lowerShear (S : Matrix m r R) : Matrix (r ⊕ m) (r ⊕ m) R :=
  Matrix.fromBlocks 1 0 S 1

def upperShear (T : Matrix r m R) : Matrix (r ⊕ m) (r ⊕ m) R :=
  Matrix.fromBlocks 1 T 0 1

theorem lowerShear_neg (S : Matrix m r R) : lowerShear S * lowerShear (-S) = 1 := by
  simp [lowerShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem upperShear_neg (T : Matrix r m R) : upperShear T * upperShear (-T) = 1 := by
  simp [upperShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

def lowerShearUnit (S : Matrix m r R) : (Matrix (r ⊕ m) (r ⊕ m) R)ˣ where
  val := lowerShear S
  inv := lowerShear (-S)
  val_inv := lowerShear_neg S
  inv_val := by simpa using lowerShear_neg (-S)

def upperShearUnit (T : Matrix r m R) : (Matrix (r ⊕ m) (r ⊕ m) R)ˣ where
  val := upperShear T
  inv := upperShear (-T)
  val_inv := upperShear_neg T
  inv_val := by simpa using upperShear_neg (-T)

def blockDiagonalUnit (a : (Matrix r r R)ˣ) (b : (Matrix m m R)ˣ) :
    (Matrix (r ⊕ m) (r ⊕ m) R)ˣ where
  val := Matrix.fromBlocks ↑a 0 0 ↑b
  inv := Matrix.fromBlocks ↑a⁻¹ 0 0 ↑b⁻¹
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

end ShearAlgebra

section TransferAlgebra
variable {F : Type uF} {R : Type uR} {r : Type ur} {m : Type um} [Field F] [Ring R] [Algebra F R]
variable [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]

def transferMatrix (q : F) (P : Matrix m m R) (U : Matrix m r R) (V : Matrix r m R) :
    Matrix (r ⊕ m) (r ⊕ m) R :=
  Matrix.fromBlocks (q • 1) V U (q⁻¹ • (U * V - P - q • (1 - P)))

theorem transferMatrix_factorization (q : F) (hq : q ≠ 0) (P : Matrix m m R)
    (U : Matrix m r R) (V : Matrix r m R) :
    lowerShear (q⁻¹ • U) *
      Matrix.fromBlocks (q • (1 : Matrix r r R)) 0 0
        (projectionReweight P (-q⁻¹) (-1 : F)) * upperShear (q⁻¹ • V) =
      transferMatrix q P U V := by
  rw [lowerShear, upperShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [inv_mul_cancel₀ hq, mul_inv_cancel₀ hq, one_smul]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp
  · simp only [projectionReweight, neg_smul, one_smul, smul_sub, smul_smul,
      inv_mul_cancel₀ hq, mul_one, one_smul]
    abel

theorem transferMatrix_isUnit (q : F) (hq : q ≠ 0) (P : Matrix m m R)
    (hP : P * P = P) (U : Matrix m r R) (V : Matrix r m R) :
    IsUnit (transferMatrix q P U V) := by
  have hu : IsUnit (q • (1 : Matrix r r R)) := by
    rw [Algebra.smul_def, mul_one]
    exact (isUnit_iff_ne_zero.mpr hq).map (algebraMap F (Matrix r r R))
  obtain ⟨a, ha⟩ := hu
  let b := projectionReweightUnit P hP (-q⁻¹) (-1 : F)
    (neg_ne_zero.mpr (inv_ne_zero hq)) (neg_ne_zero.mpr one_ne_zero)
  rw [← transferMatrix_factorization q hq P U V]
  have hd : IsUnit (Matrix.fromBlocks (q • (1 : Matrix r r R)) 0 0
      (projectionReweight P (-q⁻¹) (-1 : F))) := by
    refine ⟨blockDiagonalUnit a b, ?_⟩
    change Matrix.fromBlocks (a : Matrix r r R) 0 0
      (projectionReweight P (-q⁻¹) (-1 : F)) = _
    rw [ha]
  exact (lowerShearUnit (q⁻¹ • U)).isUnit.mul hd |>.mul (upperShearUnit (q⁻¹ • V)).isUnit

end TransferAlgebra

end GroupRingDeterminant

end

end OAI
