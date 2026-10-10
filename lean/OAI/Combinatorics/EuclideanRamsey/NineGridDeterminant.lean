import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace OAI

/-! The denominator-cleared matrix has rows and columns indexed by `Fin 3 × Fin 3`.
At the grid `(0, 1, -1)²`, its polynomial evaluation is a Kronecker square
with nonzero determinant. -/

noncomputable section

namespace EuclideanRamsey.NineGrid

open scoped Kronecker

abbrev Index := Fin 3 × Fin 3
abbrev Vars := Index ⊕ Index
abbrev Poly := MvPolynomial Vars ℚ

/-- The denominator-cleared rational parametrization coordinates. -/
def q {R : Type*} [CommRing R] (z : R) : Fin 3 → R :=
  ![1 + z ^ 2, 1 - z ^ 2, 2 * z]

def T (i : Index) : Poly := MvPolynomial.X (Sum.inl i)
def U (i : Index) : Poly := MvPolynomial.X (Sum.inr i)

/-- Polynomial evaluation rows before dividing by (1+T²)(1+U²). -/
def E : Matrix Index Index Poly :=
  fun i j => q (T i) j.1 * q (U i) j.2

def grid : Fin 3 → ℚ := ![0, 1, -1]

/-- T_(a,b) is sent to grid a, and U_(a,b) to grid b. -/
def gridAssignment : Vars → ℚ
  | Sum.inl i => grid i.1
  | Sum.inr i => grid i.2

def gridEval : Poly →+* ℚ := MvPolynomial.eval gridAssignment

/-- The evaluated one-parameter matrix C'. -/
def C : Matrix (Fin 3) (Fin 3) ℚ := fun i j => q (grid i) j

lemma map_q {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) (a : Fin 3) :
    f (q z a) = q (f z) a := by
  fin_cases a <;> simp [q, map_ofNat]

@[simp] lemma gridEval_T (i : Index) : gridEval (T i) = grid i.1 := by
  simp [gridEval, T, gridAssignment]

@[simp] lemma gridEval_U (i : Index) : gridEval (U i) = grid i.2 := by
  simp [gridEval, U, gridAssignment]

/-- Exact rational entries, with rows indexed in the order 0,1,2. -/
lemma C_eq : C = ![![1, 1, 0], ![2, 0, 2], ![2, 0, -2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C, q, grid]

lemma det_C : Matrix.det C = 8 := by
  rw [Matrix.det_fin_three]
  norm_num [C, q, grid, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The evaluation is on the polynomial ring alone. -/
lemma evaluated_E : gridEval.mapMatrix E = C ⊗ₖ C := by
  ext i j
  rcases i with ⟨r, s⟩
  rcases j with ⟨a, b⟩
  change gridEval (q (T (r, s)) a * q (U (r, s)) b) = C r a * C s b
  rw [map_mul, map_q, map_q, gridEval_T, gridEval_U]
  rfl

lemma det_evaluated_E : Matrix.det (gridEval.mapMatrix E) = (8 : ℚ) ^ 6 := by
  simp only [evaluated_E, Matrix.det_kronecker, det_C, Fintype.card_fin]
  norm_num

lemma gridEval_det_E : gridEval (Matrix.det E) = (8 : ℚ) ^ 6 := by
  rw [RingHom.map_det]
  exact det_evaluated_E

/-- The full denominator-cleared nine-row polynomial determinant is nonzero. -/
theorem det_E_ne_zero : Matrix.det E ≠ 0 := by
  intro hzero
  have h := gridEval_det_E
  rw [hzero, map_zero] at h
  norm_num at h

end EuclideanRamsey.NineGrid

end

end OAI
