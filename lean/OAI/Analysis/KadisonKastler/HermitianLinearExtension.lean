import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes

namespace OAI

/-! # Complexification of self-adjoint pairing identities -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem complexLinear_eq_of_selfAdjoint (F G : A →ₗ[ℂ] ℂ)
    (h : ∀ x : selfAdjoint A, F x.val = G x.val) : F = G := by
  ext x
  rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_add, map_smul, map_smul,
    h (realPart x), h (imaginaryPart x)]

theorem hermitianLinear_eq_of_selfAdjoint_real (F G : A →ₗ[ℂ] ℂ)
    (hF : ∀ x, F (star x) = star (F x))
    (hG : ∀ x, G (star x) = star (G x))
    (h : ∀ x : selfAdjoint A, (F x.val).re = (G x.val).re) : F = G := by
  apply complexLinear_eq_of_selfAdjoint F G
  intro x
  have hf := congrArg Complex.im (hF x.val)
  have hg := congrArg Complex.im (hG x.val)
  rw [x.property.star_eq, Complex.star_def, Complex.conj_im] at hf hg
  apply Complex.ext (h x)
  linarith

end

end KadisonKastler

end OAI
