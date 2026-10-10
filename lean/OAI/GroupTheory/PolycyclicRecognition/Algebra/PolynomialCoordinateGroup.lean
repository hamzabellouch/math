import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorSchemes

namespace OAI

/-! # The group carried by a polynomial coordinate law

This type keeps the group multiplication distinct from vector addition. The
exponential-coordinate bijection is the identity on underlying points.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A separate type for the group structure supplied by a coordinate law. -/
def PolynomialCoordinateGroup (m : V → V → V) (_h : PolynomialGroupLaws m) := V

namespace PolynomialCoordinateGroup

variable (m : V → V → V) (h : PolynomialGroupLaws m)

instance : Group (PolynomialCoordinateGroup m h) where
  mul x y := m x y
  mul_assoc := h.1
  one := (0 : V)
  one_mul := h.2.1
  mul_one := h.2.2.1
  inv x := -(show V from x)
  inv_mul_cancel := h.2.2.2.1

/-- Exponential coordinates identify the underlying sets bijectively. -/
def exp : V ≃ PolynomialCoordinateGroup m h := Equiv.refl _

@[simp] theorem exp_zero : exp m h 0 = 1 := rfl

@[simp] theorem exp_neg (x : V) : exp m h (-x) = (exp m h x)⁻¹ := rfl

theorem exp_add_smul (x : V) (s t : ℝ) :
    exp m h ((s + t) • x) = exp m h (s • x) * exp m h (t • x) :=
  (h.2.2.2.2 x s t).symm

@[simp] theorem exp_mul (x y : V) : exp m h (m x y) = exp m h x * exp m h y := rfl

end PolynomialCoordinateGroup

/-- A word evaluated directly by the polynomial multiplication. -/
def polynomialWord (m : V → V → V) (X : I → V) : List (I × ℝ) → V
  | [] => 0
  | (i, t) :: w => m (t • X i) (polynomialWord m X w)

/-- The direct polynomial evaluation is exactly the generator group word. -/
theorem exp_polynomialWord (m : V → V → V) (h : PolynomialGroupLaws m)
    (X : I → V) (w : List (I × ℝ)) :
    PolynomialCoordinateGroup.exp m h (polynomialWord m X w) =
      generatorGroupWord X (PolynomialCoordinateGroup.exp m h) w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    change PolynomialCoordinateGroup.exp m h
      (m (t • X i) (polynomialWord m X w)) = _
    rw [PolynomialCoordinateGroup.exp_mul, ih, generatorGroupWord_cons]

end PolycyclicRecognition

end

end OAI
