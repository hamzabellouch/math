import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliBasis
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot

namespace OAI

/-! Exact scalar arithmetic for the H,T,CNOT history compiler.  A real
scalar is a+b/sqrt(2); a complex scalar consists of two such pairs.  The
representation is rational data throughout, including multiplication. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar

abbrev RealScalar := ℚ × ℚ
abbrev Scalar := RealScalar × RealScalar

def realRat (a : ℚ) : RealScalar := (a,0)
def realAdd (x y : RealScalar) : RealScalar := (x.1+y.1,x.2+y.2)
def realNeg (x : RealScalar) : RealScalar := (-x.1,-x.2)
def realSub (x y : RealScalar) : RealScalar := realAdd x (realNeg y)
def realMul (x y : RealScalar) : RealScalar :=
  (x.1*y.1+x.2*y.2/2,x.1*y.2+x.2*y.1)
def rat (a : ℚ) : Scalar := (realRat a,realRat 0)
def add (x y : Scalar) : Scalar := (realAdd x.1 y.1,realAdd x.2 y.2)
def neg (x : Scalar) : Scalar := (realNeg x.1,realNeg x.2)
def sub (x y : Scalar) : Scalar := add x (neg y)
def mul (x y : Scalar) : Scalar :=
  (realSub (realMul x.1 y.1) (realMul x.2 y.2),
    realAdd (realMul x.1 y.2) (realMul x.2 y.1))
def conj (x : Scalar) : Scalar := (x.1,realNeg x.2)
def sqrtHalf : Scalar := ((0,1),(0,0))
def imaginary : Scalar := ((0,0),(1,0))
def realPart (x : Scalar) : Scalar := (x.1,realRat 0)
def imagPart (x : Scalar) : Scalar := (x.2,realRat 0)

noncomputable def realValue (x : RealScalar) : ℝ :=
  (x.1:ℝ)+(x.2:ℝ)*Real.sqrt (1/2:ℝ)
noncomputable def value (x : Scalar) : ℂ :=
  (realValue x.1:ℂ)+(realValue x.2:ℂ)*Complex.I

@[simp] theorem realValue_rat (a : ℚ) : realValue (realRat a) = (a:ℝ) := by
  simp [realValue,realRat]

@[simp] theorem realValue_add (x y : RealScalar) :
    realValue (realAdd x y) = realValue x+realValue y := by
  simp only [realValue,realAdd,Rat.cast_add]
  ring

@[simp] theorem realValue_neg (x : RealScalar) : realValue (realNeg x) = -realValue x := by
  simp only [realValue,realNeg,Rat.cast_neg]
  ring

@[simp] theorem realValue_sub (x y : RealScalar) :
    realValue (realSub x y) = realValue x-realValue y := by
  simp [realSub,sub_eq_add_neg]

@[simp] theorem realValue_mul (x y : RealScalar) :
    realValue (realMul x y) = realValue x*realValue y := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)
  simp only [realValue,realMul,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
  linear_combination -(x.2:ℝ)*(y.2:ℝ)*hs

@[simp] theorem value_re (x : Scalar) : (value x).re = realValue x.1 := by
  simp [value]

@[simp] theorem value_im (x : Scalar) : (value x).im = realValue x.2 := by
  simp [value]

@[simp] theorem value_rat (a : ℚ) : value (rat a) = (a:ℂ) := by
  simp [value,rat]

@[simp] theorem value_add (x y : Scalar) : value (add x y) = value x+value y := by
  apply Complex.ext <;> simp [add]

@[simp] theorem value_neg (x : Scalar) : value (neg x) = -value x := by
  apply Complex.ext <;> simp [neg]

@[simp] theorem value_sub (x y : Scalar) : value (sub x y) = value x-value y := by
  simp [sub,sub_eq_add_neg]

@[simp] theorem value_mul (x y : Scalar) : value (mul x y) = value x*value y := by
  apply Complex.ext <;> simp [mul,Complex.mul_re,Complex.mul_im]

@[simp] theorem value_conj (x : Scalar) : value (conj x) = star (value x) := by
  apply Complex.ext <;> simp [conj]

@[simp] theorem value_sqrtHalf : value sqrtHalf = bellScale := by
  simp [value,sqrtHalf,realValue,bellScale]

@[simp] theorem value_imaginary : value imaginary = Complex.I := by
  simp [value,imaginary,realValue]

@[simp] theorem value_realPart (x : Scalar) : value (realPart x) = ((value x).re:ℂ) := by
  simp [value,realPart]

@[simp] theorem value_imagPart (x : Scalar) : value (imagPart x) = ((value x).im:ℂ) := by
  simp [value,imagPart]

def sum : List Scalar → Scalar
  | [] => rat 0
  | x::xs => add x (sum xs)

def product : List Scalar → Scalar
  | [] => rat 1
  | x::xs => mul x (product xs)

@[simp] theorem value_sum (xs : List Scalar) : value (sum xs) = (xs.map value).sum := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih => simp [sum,ih]

@[simp] theorem value_product (xs : List Scalar) : value (product xs) = (xs.map value).prod := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih => simp [product,ih]

def sample (k : ℕ) (x : RealScalar) : ℚ :=
  x.1+x.2*RationalSquareRoot.value (k,1/2)

theorem sample_error (k : ℕ) (x : RealScalar) :
    |(sample k x:ℝ)-realValue x| ≤ |(x.2:ℝ)| * (2:ℝ)⁻¹^k := by
  have h := RationalSquareRoot.value_error k (q := 1/2) (by norm_num)
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
  have he : (sample k x:ℝ)-realValue x =
      (x.2:ℝ)*((RationalSquareRoot.value (k,1/2):ℝ)-Real.sqrt (1/2:ℝ)) := by
    simp only [sample,realValue,Rat.cast_add,Rat.cast_mul]
    ring
  rw [he,abs_mul]
  simpa only [one_div] using mul_le_mul_of_nonneg_left h (abs_nonneg (x.2:ℝ))

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
