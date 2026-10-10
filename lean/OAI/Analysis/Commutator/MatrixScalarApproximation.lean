import Mathlib
import OAI.Analysis.Commutator.MatrixApproximation
import OAI.Analysis.Commutator.MatrixExpectation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixApproximation

open TracialGNS

section Norm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma trace_norm_le_vector (hone : τ 1=1) (a : A) : ‖τ a‖≤‖algebraVector τ a‖ := by
  have hi : inner ℂ (algebraVector τ 1) (algebraVector τ a)=τ a := by
    simp only [inner_algebraVector,star_one,one_mul]
  rw [←hi]
  have h1 : ‖algebraVector τ 1‖=1 := by
    exact vacuum_norm τ hone
  simpa only [h1,one_mul] using norm_inner_le_norm (𝕜:=ℂ) (algebraVector τ 1) (algebraVector τ a)

end Norm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hnormal hfaith hone in
theorem exists_scalar_expectation (hfac : FactorCorner.IsFactor M)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) (y : M) (hy : IsSelfAdjoint y)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I)
      (φ : Matrix I I ℂ →⋆ₐ[ℂ] M),
      Function.Injective φ ∧ 2≤Fintype.card I ∧
      ‖algebraVector τ (MatrixExpectation.expectation φ y-τ y • (1:M))‖<ε := by
  obtain ⟨I,hI,hdec,hne,φ,x,hφ,hcard,he⟩ :=
    exists_matrix_approximation M τ hτ hnormal hfaith hone hfac hdiffuse y hy (half_pos hε)
  let : Fintype I := hI
  let : DecidableEq I := hdec
  let : Nonempty I := hne
  refine ⟨I,hI,hdec,hne,φ,hφ,hcard,?_⟩
  have heq : MatrixExpectation.expectation φ y-τ y • (1:M)=
      MatrixExpectation.expectation φ (y-φ x)-τ (y-φ x) • (1:M) := by
    rw [map_sub,MatrixExpectation.on_matrix_trace φ τ hτ hone,map_sub,sub_smul]
    abel
  have hn : ‖algebraVector τ (τ (y-φ x) • (1:M))‖≤‖algebraVector τ (y-φ x)‖ := by
    rw [map_smul,norm_smul]
    have h1 : ‖algebraVector τ (1:M)‖=1 := by
      exact vacuum_norm τ hone
    rw [h1,mul_one]
    exact trace_norm_le_vector τ hone _
  rw [heq,map_sub]
  calc
    _≤‖algebraVector τ (MatrixExpectation.expectation φ (y-φ x))‖+
        ‖algebraVector τ (τ (y-φ x) • (1:M))‖ := norm_sub_le _ _
    _≤2*‖algebraVector τ (y-φ x)‖ := by
      linarith [MatrixExpectation.norm_vector_le φ τ hτ (y-φ x)]
    _<ε := by linarith

end Kadison.MatrixApproximation

end

end
end

end OAI
