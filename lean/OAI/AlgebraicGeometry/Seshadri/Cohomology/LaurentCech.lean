import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentTails

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
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] Q]

theorem cokernel_finite [Module.Finite K[X] N]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y)
    (opposite_denominators : ∀ x : Q, ∃ n : ℕ, ∃ y : P,
      ((Polynomial.X : K[X])^n) • g y = x) :
    Module.Finite K (Q ⧸ ((f.restrictScalars K).range ⊔ g.range)) := by
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
  apply LaurentTails.quotient_finite (A := (f.restrictScalars K).range) (B := g.range)
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    change f ((Polynomial.X : K[X]) • y) = (T 1 : K[T;T⁻¹]) • f y
    rw [map_smul, pos1]
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
  · intro x
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away (Polynomial.X : K[X]) f).surj _ _ x
    refine ⟨n, y, ?_⟩
    change f y = (T (n : ℤ) : K[T;T⁻¹]) • x
    rw [pos]
    exact hy.symm
  · intro x
    obtain ⟨n,y,hy⟩ := opposite_denominators x
    refine ⟨n,y,?_⟩
    rw [← hy, ← pos n, cancel n]
end
end MaximalSeshadri.LaurentCech
end


end
end

end OAI
