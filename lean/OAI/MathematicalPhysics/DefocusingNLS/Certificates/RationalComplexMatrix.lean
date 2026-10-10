import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace OAI

/-! Exact complex rational arithmetic for the finite profile certificate. -/

namespace DefocusingNLS.ProfileCertificate

abbrev RationalComplex := QuadraticAlgebra ℚ (-1) 0

namespace RationalComplex

def normSq (z : RationalComplex) : ℚ := z.re ^ 2 + z.im ^ 2

def absOne (z : RationalComplex) : ℚ := |z.re| + |z.im|

def quotient (z w : RationalComplex) : RationalComplex :=
  ⟨(z.re * w.re + z.im * w.im) / normSq w,
    (z.im * w.re - z.re * w.im) / normSq w⟩

noncomputable def toComplex : RationalComplex →+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by apply Complex.ext <;> simp
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by apply Complex.ext <;> simp
  map_mul' z w := by apply Complex.ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]; ring

@[simp] theorem toComplex_re (z : RationalComplex) : (toComplex z).re = z.re := rfl
@[simp] theorem toComplex_im (z : RationalComplex) : (toComplex z).im = z.im := rfl

@[simp] theorem normSq_toComplex (z : RationalComplex) :
    Complex.normSq (toComplex z) = (normSq z : ℝ) := by
  simp [Complex.normSq_apply, normSq, pow_two]

theorem norm_toComplex_le_absOne (z : RationalComplex) :
    ‖toComplex z‖ ≤ (absOne z : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (toComplex z)
  simpa [absOne] using h

@[simp] theorem toComplex_quotient (z w : RationalComplex) :
    toComplex (quotient z w) = toComplex z / toComplex w := by
  apply Complex.ext <;> simp [quotient, Complex.div_re, Complex.div_im, normSq, Complex.normSq_apply, pow_two, add_div, sub_div]

end RationalComplex

/-- A computational four-entry matrix, avoiding dependent finite-index evaluation. -/
@[ext] structure Matrix2 (R : Type*) where
  a : R
  b : R
  c : R
  d : R
  deriving DecidableEq

namespace Matrix2

variable {R S : Type*}

def zero [Zero R] : Matrix2 R := ⟨0, 0, 0, 0⟩
def one [Zero R] [One R] : Matrix2 R := ⟨1, 0, 0, 1⟩
def add [Add R] (x y : Matrix2 R) : Matrix2 R :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def mul [Add R] [Mul R] (x y : Matrix2 R) : Matrix2 R :=
  ⟨x.a*y.a+x.b*y.c, x.a*y.b+x.b*y.d,
   x.c*y.a+x.d*y.c, x.c*y.b+x.d*y.d⟩
def scale [Mul R] (r : R) (x : Matrix2 R) : Matrix2 R :=
  ⟨r*x.a, r*x.b, r*x.c, r*x.d⟩
def map (f : R → S) (x : Matrix2 R) : Matrix2 S :=
  ⟨f x.a, f x.b, f x.c, f x.d⟩
def toMatrix (x : Matrix2 R) : Matrix (Fin 2) (Fin 2) R :=
  !![x.a, x.b; x.c, x.d]

@[simp] theorem toMatrix_zero [Zero R] : toMatrix (zero : Matrix2 R) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem toMatrix_one [Zero R] [One R] : toMatrix (one : Matrix2 R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem toMatrix_add [Add R] (x y : Matrix2 R) :
    toMatrix (add x y) = toMatrix x + toMatrix y := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem toMatrix_mul [Semiring R] (x y : Matrix2 R) :
    toMatrix (mul x y) = toMatrix x * toMatrix y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] theorem toMatrix_scale [Mul R] (r : R) (x : Matrix2 R) :
    toMatrix (scale r x) = r • toMatrix x := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] theorem toMatrix_map (f : R → S) (x : Matrix2 R) :
    toMatrix (map f x) = (toMatrix x).map f := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

end Matrix2

end DefocusingNLS.ProfileCertificate

end OAI
