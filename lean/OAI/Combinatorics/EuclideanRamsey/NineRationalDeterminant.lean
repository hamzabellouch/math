import OAI.Combinatorics.EuclideanRamsey.NineGridDeterminant
import OAI.Combinatorics.EuclideanRamsey.IndependentTensor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-! Clearing denominators transfers the polynomial determinant to a faithful
rational-function realization. Renaming variables transports the result to
any equivalent set of nine row labels. -/

noncomputable section

namespace EuclideanRamsey.NineRational

abbrev Index := NineGrid.Index
abbrev Poly := NineGrid.Poly
abbrev K := IndependentTensor.JointField Index

/-- Actual rational-coordinate vector, including its constant first entry. -/
def r {F : Type*} [Field F] (z : F) : Fin 3 → F :=
  ![1, (1 - z ^ 2) / (1 + z ^ 2), (2 * z) / (1 + z ^ 2)]

lemma polynomial_denominator_ne_zero (v : NineGrid.Vars) :
    (1 + (MvPolynomial.X v : Poly) ^ 2) ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval (fun _ : NineGrid.Vars => (0 : ℚ))) hz
  norm_num at h

lemma mapped_denominator_ne_zero {F : Type*} [Field F]
    (f : Poly →+* F) (hf : Function.Injective f) (v : NineGrid.Vars) :
    1 + f (MvPolynomial.X v) ^ 2 ≠ 0 := by
  intro hz
  apply polynomial_denominator_ne_zero v
  apply hf
  simpa only [map_add, map_one, map_pow, map_zero] using hz

lemma clear_r {F : Type*} [Field F] (z : F) (hz : 1 + z ^ 2 ≠ 0)
    (a : Fin 3) : (1 + z ^ 2) * r z a = NineGrid.q z a := by
  fin_cases a <;> simp [r, NineGrid.q] <;> field_simp [hz]

/-- The actual rational-coordinate matrix in any faithful polynomial realization. -/
def genericMatrix {F : Type*} [Field F] (f : Poly →+* F) : Matrix Index Index F :=
  fun i j => r (f (NineGrid.T i)) j.1 * r (f (NineGrid.U i)) j.2

def rowDenominator {F : Type*} [Field F] (f : Poly →+* F) (i : Index) : F :=
  (1 + f (NineGrid.T i) ^ 2) * (1 + f (NineGrid.U i) ^ 2)

/-- Multiplying each row by its denominator gives the polynomial matrix. -/
lemma cleared_matrix {F : Type*} [Field F] (f : Poly →+* F)
    (hf : Function.Injective f) :
    f.mapMatrix NineGrid.E = Matrix.diagonal (rowDenominator f) * genericMatrix f := by
  ext i j
  rw [Matrix.diagonal_mul]
  change f (NineGrid.q (NineGrid.T i) j.1 * NineGrid.q (NineGrid.U i) j.2) =
    ((1 + f (NineGrid.T i) ^ 2) * (1 + f (NineGrid.U i) ^ 2)) *
      (r (f (NineGrid.T i)) j.1 * r (f (NineGrid.U i)) j.2)
  rw [map_mul, NineGrid.map_q, NineGrid.map_q]
  rw [← clear_r (f (NineGrid.T i)) (mapped_denominator_ne_zero f hf (Sum.inl i)) j.1,
    ← clear_r (f (NineGrid.U i)) (mapped_denominator_ne_zero f hf (Sum.inr i)) j.2]
  ring

/-- The rational-coordinate matrix has nonzero determinant in every faithful realization. -/
theorem det_genericMatrix_ne_zero {F : Type*} [Field F]
    (f : Poly →+* F) (hf : Function.Injective f) :
    Matrix.det (genericMatrix f) ≠ 0 := by
  have hpoly : f (Matrix.det NineGrid.E) ≠ 0 := by
    intro hz
    apply NineGrid.det_E_ne_zero
    apply hf
    simpa only [map_zero] using hz
  have hcleared : Matrix.det (f.mapMatrix NineGrid.E) ≠ 0 := by
    rw [← f.map_det]
    exact hpoly
  intro hz
  apply hcleared
  rw [cleared_matrix f hf, Matrix.det_mul, hz, mul_zero]

/-- The polynomial inclusion into the doubled-variable fraction field. -/
def polynomialInclusion : Poly →+* K := algebraMap Poly K

def t (i : Index) : K := polynomialInclusion (NineGrid.T i)
def u (i : Index) : K := polynomialInclusion (NineGrid.U i)

def M : Matrix Index Index K := fun i j => r (t i) j.1 * r (u i) j.2

theorem det_M_ne_zero : Matrix.det M ≠ 0 :=
  det_genericMatrix_ne_zero polynomialInclusion (IsFractionRing.injective Poly K)

section Relabel

variable {ι : Type*}

/-- Independent rational-function variables with arbitrary row labels. -/
def tVar (i : ι) : IndependentTensor.JointField ι :=
  algebraMap (IndependentTensor.JointPoly ι) (IndependentTensor.JointField ι)
    (MvPolynomial.X (Sum.inl i))

def uVar (i : ι) : IndependentTensor.JointField ι :=
  algebraMap (IndependentTensor.JointPoly ι) (IndependentTensor.JointField ι)
    (MvPolynomial.X (Sum.inr i))

/-- Rename the polynomial variables bijectively and include them in the fraction field. -/
def transportPoly (e : ι ≃ Index) : Poly →+* IndependentTensor.JointField ι :=
  (algebraMap (IndependentTensor.JointPoly ι) (IndependentTensor.JointField ι)).comp
    (MvPolynomial.rename (Equiv.sumCongr e.symm e.symm)).toRingHom

lemma transportPoly_injective (e : ι ≃ Index) : Function.Injective (transportPoly e) :=
  (IsFractionRing.injective (IndependentTensor.JointPoly ι)
    (IndependentTensor.JointField ι)).comp
      (MvPolynomial.rename_injective (Equiv.sumCongr e.symm e.symm)
        (Equiv.sumCongr e.symm e.symm).injective)

/-- Both axes are reindexed by e. Columns encode the two coordinate indices. -/
def transportedMatrix (e : ι ≃ Index) : Matrix ι ι (IndependentTensor.JointField ι) :=
  (genericMatrix (transportPoly e)).submatrix e e

lemma transportedMatrix_apply (e : ι ≃ Index) (i j : ι) :
    transportedMatrix e i j = r (tVar i) (e j).1 * r (uVar i) (e j).2 := by
  simp [transportedMatrix, genericMatrix, transportPoly, NineGrid.T, NineGrid.U,
    tVar, uVar]

theorem det_transportedMatrix_ne_zero [Fintype ι] [DecidableEq ι] (e : ι ≃ Index) :
    Matrix.det (transportedMatrix e) ≠ 0 := by
  change Matrix.det ((genericMatrix (transportPoly e)).submatrix e e) ≠ 0
  rw [Matrix.det_submatrix_equiv_self]
  exact det_genericMatrix_ne_zero (transportPoly e) (transportPoly_injective e)

end Relabel

/-- Concrete row/column enumeration of the nine tensor coordinates. -/
def fin9Equiv : Fin 9 ≃ Index := (finProdFinEquiv : Index ≃ Fin (3 * 3)).symm

def fin9Matrix : Matrix (Fin 9) (Fin 9) (IndependentTensor.JointField (Fin 9)) :=
  transportedMatrix fin9Equiv

lemma fin9Matrix_apply (i j : Fin 9) :
    fin9Matrix i j = r (tVar i) (fin9Equiv j).1 * r (uVar i) (fin9Equiv j).2 :=
  transportedMatrix_apply fin9Equiv i j

theorem det_fin9Matrix_ne_zero : Matrix.det fin9Matrix ≠ 0 :=
  det_transportedMatrix_ne_zero fin9Equiv

end EuclideanRamsey.NineRational

end

end OAI
