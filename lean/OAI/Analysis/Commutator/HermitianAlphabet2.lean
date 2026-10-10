import Mathlib
import OAI.Analysis.Commutator.MatrixGNS
import OAI.Analysis.Commutator.HermitianAlphabet

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open MatrixAlphabet

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

include hτ h1 in
lemma centered_normalizedLetter (o i : I) (hi : i ≠ o) :
    (centeredStageVector τ φ (normalizedLetter o i) : τ.GNS) =
      stageVector τ φ (normalizedLetter o i) := by
  rw [stage_centered τ hτ h1, trace_normalizedLetter o i hi, mul_zero, zero_smul, sub_zero]

include hτ h1 in
lemma normalizedLetter_orthonormal {J : Type*} (o : I) (b : J ↪ I)
    (hb : ∀ j, b j ≠ o) :
    Orthonormal ℂ (fun j => centeredStageVector τ φ (normalizedLetter o (b j))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (centeredStageVector τ φ (normalizedLetter o (b i)) : τ.GNS)
    (centeredStageVector τ φ (normalizedLetter o (b j)) : τ.GNS) = _
  rw [centered_normalizedLetter τ hτ h1 φ o _ (hb i),
    centered_normalizedLetter τ hτ h1 φ o _ (hb j), stage_inner τ hτ h1,
    star_normalizedLetter, normalized_trace_mul o _ _ (hb i) (hb j)]
  simp only [EmbeddingLike.apply_eq_iff_eq]

end Kadison.TracialGNS
end

end OAI
