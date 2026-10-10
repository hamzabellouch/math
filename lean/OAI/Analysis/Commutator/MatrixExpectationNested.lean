import Mathlib
import OAI.Analysis.Commutator.MatrixExpectation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixExpectation

open TracialGNS

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] [Nonempty J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hsub : φ.range≤ψ.range)

omit [PartialOrder A] [StarOrderedRing A] [Nonempty J] in
include hsub in
lemma nested_fixed (a : A) : expectation φ (expectation ψ a)=expectation ψ a := by
  apply fixes
  intro x
  obtain ⟨y,hy⟩ := hsub (show φ x∈φ.range from ⟨x,rfl⟩)
  change ψ y=φ x at hy
  rw [←hy]
  exact commutes ψ a y

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

omit [Nonempty J] in
include hsub hτ in
lemma nested_vector (a : A) :
    algebraVector τ (expectation ψ (expectation φ a))=algebraVector τ (expectation ψ a) := by
  apply (algebraVector_dense τ).eq_of_inner_left ℂ
  intro b
  rw [inner_symm ψ τ hτ,inner_symm φ τ hτ,nested_fixed φ ψ hsub,inner_symm ψ τ hτ]

omit [PartialOrder A] [StarOrderedRing A] in
lemma fixes_scalar (z : ℂ) : expectation φ (z • (1:A))=z • (1:A) := by
  rw [map_smul,fixes φ 1 (fun x => by rw [mul_one,one_mul])]

include hsub hτ in
lemma nested_norm_le (a : A) (z : ℂ) :
    ‖algebraVector τ (expectation ψ a-z • (1:A))‖≤
      ‖algebraVector τ (expectation φ a-z • (1:A))‖ := by
  have he : algebraVector τ (expectation ψ (expectation φ a-z • (1:A)))=
      algebraVector τ (expectation ψ a-z • (1:A)) := by
    rw [map_sub,fixes_scalar,map_sub,map_sub,nested_vector φ ψ hsub τ hτ]
  rw [←he]
  exact norm_vector_le ψ τ hτ _

end Kadison.MatrixExpectation

end

end
end

end OAI
