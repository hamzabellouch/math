import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OAI

/-! # Coordinates adapted to a chosen lift of an infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerQuotientHeight (g : G) : ℤ := (q g).toAdd

@[simp] theorem integerQuotientHeight_mul (g h : G) :
    integerQuotientHeight q (g * h) = integerQuotientHeight q g + integerQuotientHeight q h := by
  simp [integerQuotientHeight]

@[simp] theorem integerQuotientHeight_kernel (n : q.ker) : integerQuotientHeight q n = 0 := by
  exact congrArg Multiplicative.toAdd n.property

include ht in
@[simp] theorem integerQuotientHeight_lift_zpow (i : ℤ) :
    integerQuotientHeight q (t ^ i) = i := by
  simp [integerQuotientHeight, ht]

def integerQuotientPart (g : G) : q.ker :=
  ⟨g * t ^ (-integerQuotientHeight q g), by
    change q (g * t ^ (-integerQuotientHeight q g)) = 1
    apply Multiplicative.toAdd.injective
    simp [map_mul, map_zpow, ht, integerQuotientHeight]⟩

theorem integerQuotientPart_decompose (g : G) :
    (integerQuotientPart q t ht g : G) * t ^ integerQuotientHeight q g = g := by
  simp [integerQuotientPart, zpow_neg, mul_assoc]

@[simp] theorem integerQuotientPart_kernel_mul (n : q.ker) (g : G) :
    integerQuotientPart q t ht ((n : G) * g) = n * integerQuotientPart q t ht g := by
  apply Subtype.ext
  simp [integerQuotientPart, mul_assoc]

@[simp] theorem integerQuotientPart_lift_zpow (i : ℤ) :
    integerQuotientPart q t ht (t ^ i) = 1 := by
  apply Subtype.ext
  simp [integerQuotientPart, integerQuotientHeight_lift_zpow q t ht, zpow_neg]

def integerQuotientCoordinates : G ≃ ℤ × q.ker where
  toFun g := (integerQuotientHeight q g, integerQuotientPart q t ht g)
  invFun p := (p.2 : G) * t ^ p.1
  left_inv g := integerQuotientPart_decompose q t ht g
  right_inv p := by
    rcases p with ⟨i, n⟩
    apply Prod.ext
    · simp [integerQuotientHeight_lift_zpow q t ht]
    · simp [integerQuotientPart_lift_zpow q t ht]

theorem integerQuotientPart_lift_mul (g : G) :
    integerQuotientPart q t ht (t * g) =
      MulAut.conjNormal (H := q.ker) t (integerQuotientPart q t ht g) := by
  apply Subtype.ext
  change t * g * t ^ (-integerQuotientHeight q (t * g)) =
    t * (g * t ^ (-integerQuotientHeight q g)) * t⁻¹
  have hh : integerQuotientHeight q t = 1 := by simp [integerQuotientHeight, ht]
  rw [integerQuotientHeight_mul, hh]
  have he : -(1 + integerQuotientHeight q g) = -integerQuotientHeight q g + (-1) := by omega
  rw [he, zpow_add, zpow_neg_one]
  group

end PolycyclicRecognition

end

end OAI
