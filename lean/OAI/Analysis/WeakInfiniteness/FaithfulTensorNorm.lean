import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorMatrixNorm

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorRightRepresentation

variable {n H K L B : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma map_tensorCoefficientMatrix
    (b : OrthonormalBasis n ℂ H) (T : H →L[ℂ] H) (a : B)
    (φ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    CStarMatrix.mapₙₐ φ (tensorCoefficientMatrix b T a) =
      tensorCoefficientMatrix b T (φ a) := by
  apply CStarMatrix.ext
  intro i j
  change φ ((b.repr (T (b j)) i) • a) = (b.repr (T (b j)) i) • φ a
  exact map_smul φ _ _

lemma tensor_norm_le_faithful_finite_left {ι : Type*} (s : Finset ι)
    (b : OrthonormalBasis n ℂ H) (T : ι → H →L[ℂ] H) (a : ι → B)
    (φ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ψ : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hφ : Function.Injective φ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (ψ (a i))‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))‖ := by
  rw [norm_tensorCoefficientSum s b, norm_tensorCoefficientSum s b]
  let M : CStarMatrix n n B := ∑ i ∈ s, tensorCoefficientMatrix b (T i) (a i)
  have hm (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
      CStarMatrix.mapₙₐ ρ M = ∑ i ∈ s, tensorCoefficientMatrix b (T i) (ρ (a i)) := by
    simp only [M, map_sum, map_tensorCoefficientMatrix]
  have hn : CStarMatrix.mapₙₐ ψ M = ∑ i ∈ s, tensorCoefficientMatrix b (T i) (ψ (a i)) := by
    simp only [M, map_sum, map_tensorCoefficientMatrix]
  rw [← hm φ, ← hn]
  have hinj : Function.Injective (CStarMatrix.mapₙₐ φ (n := n)) := by
    intro X Y hXY
    ext i j
    apply hφ
    exact congrArg (fun Z : CStarMatrix n n (K →L[ℂ] K) => Z i j) hXY
  rw [NonUnitalStarAlgHom.norm_map (CStarMatrix.mapₙₐ φ) hinj M]
  exact NonUnitalStarAlgHom.norm_apply_le (CStarMatrix.mapₙₐ ψ) M

end TensorRightRepresentation

end WeakPureInfiniteness
end

end OAI
