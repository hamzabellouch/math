import Mathlib.Algebra.Homology.TotalComplexSymmetry

namespace OAI

/-! # The Koszul symmetry for first-quadrant chain complexes -/
namespace PolycyclicRecognition

instance natDownTotalComplexSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    intro p p' h q
    change p' + 1 = p at h
    subst p
    change (-1 : ℤˣ) ^ ((p' + 1) * q) * 1 = (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ (p' * q)
    rw [Nat.add_mul, one_mul, pow_add, mul_one, mul_comm]
  σ_ε₂ := by
    intro p q q' h
    change q' + 1 = q at h
    subst q
    change (-1 : ℤˣ) ^ (p * (q' + 1)) * (-1 : ℤˣ) ^ p = 1 * (-1 : ℤˣ) ^ (p * q')
    rw [Nat.mul_add, mul_one, pow_add, mul_assoc, Int.units_mul_self, mul_one, one_mul]

end PolycyclicRecognition

end OAI
