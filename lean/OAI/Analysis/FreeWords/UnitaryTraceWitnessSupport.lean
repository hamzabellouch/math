import Mathlib
import OAI.Analysis.FreeWords.FactorStructure

namespace OAI

noncomputable section

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_mul_unitary_norm (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (x : A) (u : unitary A) :
    ‖gnsVector τ (x * (u : A))‖ = ‖gnsVector τ x‖ := by
  have heq : τ (star (x * (u : A)) * (x * (u : A))) = τ (star x * x) := by
    rw [star_mul, htr]
    calc
      τ ((x * (u : A)) * (star (u : A) * star x)) = τ (x * star x) := by
        congr 1
        calc
          x * (u : A) * (star (u : A) * star x) = x * ((u : A) * star (u : A)) * star x := by
            simp only [mul_assoc]
          _ = x * star x := by rw [← Unitary.coe_star, Unitary.coe_mul_star_self, mul_one]
      _ = _ := htr _ _
  have hh : ‖gnsVector τ (x * (u : A))‖ ^ 2 = ‖gnsVector τ x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, gnsVector_inner, gnsVector_inner, heq]
  nlinarith [norm_nonneg (gnsVector τ (x * (u : A))), norm_nonneg (gnsVector τ x)]

theorem gnsVector_conj_sub_norm (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (x : A) (u : unitary A) :
    ‖gnsVector τ x - gnsVector τ (algebraConj u x)‖ =
      ‖gnsVector τ (x * (u : A) - (u : A) * x)‖ := by
  rw [← map_sub]
  have heq : x - algebraConj u x = (x * (u : A) - (u : A) * x) * (↑(star u) : A) := by
    simp only [Unitary.coe_star, sub_mul, algebraConj_apply]
    rw [mul_assoc x, ← Unitary.coe_star, Unitary.coe_mul_star_self, mul_one]
  rw [heq, gnsVector_mul_unitary_norm τ htr]

end

end KKFactorSupport
end

end OAI
