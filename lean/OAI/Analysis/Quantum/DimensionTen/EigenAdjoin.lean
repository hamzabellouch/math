import Mathlib

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen.Arithmetic

lemma linear_eval_mul {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (f : K[X]) (ψ : AdjoinRoot f →ₗ[K] R) (s : R)
    (hs : ∀ a, ψ (AdjoinRoot.root f * a) = s * ψ a)
    (p : K[X]) (a : AdjoinRoot f) :
    ψ (aeval (AdjoinRoot.root f) p * a) = aeval s p * ψ a := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [aeval_C, aeval_C, ← Algebra.smul_def, map_smul, Algebra.smul_def]
  | add p q hp hq =>
    simp only [map_add, add_mul, hp, hq]
  | monomial n c ih =>
    have he : C c * X ^ (n + 1) = X * (C c * X ^ n) := by ring
    rw [he, map_mul (aeval (AdjoinRoot.root f)), aeval_X, mul_assoc, hs, ih]
    simp only [map_mul, aeval_X, mul_assoc]

def algHomOfEigen {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (f : K[X]) (ψ : AdjoinRoot f →ₗ[K] R) (s : R)
    (h1 : ψ 1 = 1) (hs : ∀ a, ψ (AdjoinRoot.root f * a) = s * ψ a) :
    AdjoinRoot f →ₐ[K] R where
  toFun := ψ
  map_zero' := ψ.map_zero
  map_add' := ψ.map_add
  map_one' := h1
  map_mul' := by
    intro a b
    induction a using AdjoinRoot.induction_on with
    | ih p =>
      rw [← AdjoinRoot.aeval_eq]
      have hp := linear_eval_mul f ψ s hs p b
      have hq := linear_eval_mul f ψ s hs p 1
      simp only [mul_one, h1] at hq
      rw [hq]
      exact hp
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, Algebra.smul_def, mul_one]

@[simp] lemma algHomOfEigen_apply {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (f : K[X]) (ψ : AdjoinRoot f →ₗ[K] R) (s : R)
    (h1 : ψ 1 = 1) (hs : ∀ a, ψ (AdjoinRoot.root f * a) = s * ψ a)
    (a : AdjoinRoot f) : algHomOfEigen f ψ s h1 hs a = ψ a := rfl

end DimensionTen.Arithmetic

end
end

end OAI
