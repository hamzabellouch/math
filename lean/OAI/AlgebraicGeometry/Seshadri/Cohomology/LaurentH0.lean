import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.PolynomialLattices

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.LaurentCech
noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

theorem intersection_finite [Module.Finite K[X] N] [Module.Finite K[X] P]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y) :
    Module.Finite K ↥((f.restrictScalars K).range ⊓ g.range) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentLattices.range_intersection_finite (f.restrictScalars K) g
  · intro x
    change f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x
    rw [map_smul, pos1]
  · intro y
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
end
end MaximalSeshadri.LaurentCech
end


end
end

end OAI
