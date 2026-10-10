import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicScalar

namespace OAI

/-! Rational coefficient-height bounds for the fixed history expressions.
These bounds provide a polynomial precision budget before real evaluation. -/

namespace ContinuumCoulomb.QuantumAlgebraicScalar
open scoped BigOperators

def realHeight (x : RealScalar) : ℚ := |x.1|+|x.2|
def height (x : Scalar) : ℚ := realHeight x.1+realHeight x.2

theorem realHeight_nonnegative (x : RealScalar) : 0 ≤ realHeight x :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem height_nonnegative (x : Scalar) : 0 ≤ height x :=
  add_nonneg (realHeight_nonnegative _) (realHeight_nonnegative _)

@[simp] theorem realHeight_rat (a : ℚ) : realHeight (realRat a) = |a| := by
  simp [realHeight,realRat]

@[simp] theorem realHeight_neg (x : RealScalar) : realHeight (realNeg x) = realHeight x := by
  simp [realHeight,realNeg]

theorem realHeight_add (x y : RealScalar) :
    realHeight (realAdd x y) ≤ realHeight x+realHeight y := by
  have ha := abs_add_le x.1 y.1
  have hb := abs_add_le x.2 y.2
  dsimp only [realHeight,realAdd]
  linarith

theorem realHeight_sub (x y : RealScalar) :
    realHeight (realSub x y) ≤ realHeight x+realHeight y := by
  simpa only [realSub,realHeight_neg] using realHeight_add x (realNeg y)

theorem realHeight_mul (x y : RealScalar) :
    realHeight (realMul x y) ≤ realHeight x*realHeight y := by
  have ha := abs_add_le (x.1*y.1) (x.2*y.2/2)
  have hb := abs_add_le (x.1*y.2) (x.2*y.1)
  norm_num only [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℚ) < 2)] at ha hb
  dsimp only [realHeight,realMul]
  nlinarith [mul_nonneg (abs_nonneg x.2) (abs_nonneg y.2)]

@[simp] theorem height_rat (a : ℚ) : height (rat a) = |a| := by
  simp [height,rat]

@[simp] theorem height_neg (x : Scalar) : height (neg x) = height x := by
  simp [height,neg]

theorem height_add (x y : Scalar) : height (add x y) ≤ height x+height y := by
  have ha := realHeight_add x.1 y.1
  have hb := realHeight_add x.2 y.2
  dsimp only [height,add]
  linarith

theorem height_sub (x y : Scalar) : height (sub x y) ≤ height x+height y := by
  simpa only [sub,height_neg] using height_add x (neg y)

theorem height_mul (x y : Scalar) : height (mul x y) ≤ height x*height y := by
  have hr := realHeight_sub (realMul x.1 y.1) (realMul x.2 y.2)
  have hi := realHeight_add (realMul x.1 y.2) (realMul x.2 y.1)
  have hrr := realHeight_mul x.1 y.1
  have hii := realHeight_mul x.2 y.2
  have hri := realHeight_mul x.1 y.2
  have hir := realHeight_mul x.2 y.1
  dsimp only [height,mul]
  nlinarith

@[simp] theorem height_conj (x : Scalar) : height (conj x) = height x := by
  simp [height,conj]

@[simp] theorem height_sqrtHalf : height sqrtHalf = 1 := by
  norm_num [height,realHeight,sqrtHalf]

@[simp] theorem height_imaginary : height imaginary = 1 := by
  norm_num [height,realHeight,imaginary]

theorem height_realPart (x : Scalar) : height (realPart x) ≤ height x := by
  simp only [height,realPart,realHeight_rat,abs_zero,add_zero]
  exact le_add_of_nonneg_right (realHeight_nonnegative _)

theorem height_imagPart (x : Scalar) : height (imagPart x) ≤ height x := by
  simp only [height,imagPart,realHeight_rat,abs_zero,add_zero]
  exact le_add_of_nonneg_left (realHeight_nonnegative _)

theorem height_sum (xs : List Scalar) : height (sum xs) ≤ (xs.map height).sum := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
    change height (add x (sum xs)) ≤ height x+(xs.map height).sum
    exact (height_add x (sum xs)).trans (add_le_add (le_refl (height x)) ih)

theorem height_product (xs : List Scalar) : height (product xs) ≤ (xs.map height).prod := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih =>
    change height (mul x (product xs)) ≤ height x*(xs.map height).prod
    exact (height_mul x (product xs)).trans
      (mul_le_mul_of_nonneg_left ih (height_nonnegative x))

theorem sample_error_height (k : ℕ) (x : RealScalar) :
    |(sample k x:ℝ)-realValue x| ≤ (realHeight x:ℝ)*(2:ℝ)⁻¹^k := by
  apply (sample_error k x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h : |x.2| ≤ realHeight x := le_add_of_nonneg_left (abs_nonneg _)
  exact_mod_cast h

end ContinuumCoulomb.QuantumAlgebraicScalar

end OAI
