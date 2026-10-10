import Mathlib
import OAI.Analysis.MatrixSigning.Machines.ComplexBridge

namespace OAI

section

namespace KS.W01

namespace RationalComplex

def zero : RationalComplex := (0, 0)
def one : RationalComplex := (1, 0)
def add (z w : RationalComplex) : RationalComplex := (z.1 + w.1, z.2 + w.2)
def neg (z : RationalComplex) : RationalComplex := (-z.1, -z.2)
def mul (z w : RationalComplex) : RationalComplex :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def conj (z : RationalComplex) : RationalComplex := (z.1, -z.2)
def normSq (z : RationalComplex) : ℚ := z.1 * z.1 + z.2 * z.2
def inv (z : RationalComplex) : RationalComplex :=
  (z.1 / normSq z, -z.2 / normSq z)

@[simp] theorem toComplex_zero : toComplex zero = 0 := by
  apply Complex.ext <;> simp [toComplex, zero]

@[simp] theorem toComplex_one : toComplex one = 1 := by
  apply Complex.ext <;> simp [toComplex, one]

@[simp] theorem toComplex_add (z w : RationalComplex) :
    toComplex (add z w) = toComplex z + toComplex w := by
  apply Complex.ext <;> simp [toComplex, add]

@[simp] theorem toComplex_neg (z : RationalComplex) :
    toComplex (neg z) = -toComplex z := by
  apply Complex.ext <;> simp [toComplex, neg]

@[simp] theorem toComplex_mul (z w : RationalComplex) :
    toComplex (mul z w) = toComplex z * toComplex w := by
  apply Complex.ext <;> simp [toComplex, mul, Complex.mul_re, Complex.mul_im]

@[simp] theorem toComplex_conj (z : RationalComplex) :
    toComplex (conj z) = star (toComplex z) := by
  apply Complex.ext <;> simp [toComplex, conj]

@[simp] theorem toReal_normSq (z : RationalComplex) :
    (normSq z : ℝ) = Complex.normSq (toComplex z) := by
  simp [normSq, Complex.normSq_apply, toComplex]

@[simp] theorem toComplex_inv (z : RationalComplex) :
    toComplex (inv z) = (toComplex z)⁻¹ := by
  apply Complex.ext <;> simp [toComplex, inv, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, normSq]

end RationalComplex
end KS.W01

end

end OAI
