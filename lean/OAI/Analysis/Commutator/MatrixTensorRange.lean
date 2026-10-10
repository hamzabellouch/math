import Mathlib
import OAI.Analysis.Commutator.MatrixTensor

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.MatrixTensor

variable {A I J : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hc : ∀ x y,Commute (φ x) (ψ y))

lemma range_le (S : StarSubalgebra ℂ A) (hφ : φ.range≤S) (hψ : ψ.range≤S) :
    (representation φ ψ hc).range≤S := by
  rintro a ⟨x,rfl⟩
  change (∑ i,∑ j,x i j • (φ (Matrix.single i.1 j.1 1)*ψ (Matrix.single i.2 j.2 1)))∈S
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  exact S.smul_mem (S.mul_mem (hφ ⟨_,rfl⟩) (hψ ⟨_,rfl⟩)) _

end Kadison.MatrixTensor

end

end
end

end OAI
