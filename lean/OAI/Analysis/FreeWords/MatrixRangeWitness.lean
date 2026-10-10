import Mathlib
import OAI.Analysis.FreeWords.FiniteSubalgebraWitness
import OAI.Analysis.FreeWords.MatrixRangeCenter

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKUltraTrace KKTraceTransfer

open scoped ComplexOrder

noncomputable section

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [DecidableEq ι]

instance matrix_range_finiteDimensional (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) :
    FiniteDimensional ℂ ρ.range := by
  apply FiniteDimensional.of_surjective ρ.rangeRestrict.toLinearMap
  intro x
  obtain ⟨a,ha⟩ := x.property
  exact ⟨a,Subtype.ext ha⟩

instance matrix_range_isClosed (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) : IsClosed (ρ.range : Set A) :=
  by
  exact ρ.toLinearMap.range.closed_of_finiteDimensional

theorem matrix_range_commutator_witness (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A)
    (hρ : Function.Injective ρ) (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (h1 : τ 1=1)
    (hinj : Function.Injective (gnsVector τ)) (x : A) (hx : x∈ρ.range) :
    ∃ u : unitary A, u.val∈ρ.range ∧
      ‖gnsVector τ (x-τ x•1)‖≤2*‖gnsVector τ (x*u.val-u.val*x)‖ := by
  exact finite_subalgebra_commutator_witness ρ.range τ htr h1 hinj
    (matrix_range_center ρ hρ) x hx

end

end KKVariableUltra
end

end OAI
