import Mathlib
import OAI.Analysis.WeakInfiniteness.NuclearCompression

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
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder

universe u

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : ℕ}

omit [PartialOrder A] [StarOrderedRing A] in
def finiteCompressionLinear (v : Fin n → A) : A →ₗ[ℂ] A where
  toFun := finiteCompression v
  map_add' r s := by
    simp only [finiteCompression,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [finiteCompression,mul_smul_comm,smul_mul_assoc,Finset.smul_sum,RingHom.id_apply]

def finiteCompressionContinuous (v : Fin n → A) : A →L[ℂ] A :=
  (finiteCompressionLinear v).mkContinuous ‖∑ i,star (v i)*v i‖ (finiteCompression_norm_le v)

lemma finiteCompressionContinuous_apply (v : Fin n → A) (r : A) :
    finiteCompressionContinuous v r=finiteCompression v r := rfl

lemma finiteCompressionContinuous_norm_le (v : Fin n → A) :
    ‖finiteCompressionContinuous v‖≤‖∑ i,star (v i)*v i‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    (fun r => finiteCompression_norm_le v r)

lemma finiteCompressionContinuous_cp (v : Fin n → A) :
    CompletelyPositive (finiteCompressionContinuous v) := by
  intro m x hx
  have he_i (i : Fin n) (j k : Fin m) :
      (star (diagonalCopies m (v i))*x*diagonalCopies m (v i)) j k=
      star (v i)*x j k*v i := by
    simp [diagonalCopies,CStarMatrix.mul_apply,CStarMatrix.star_apply,Matrix.diagonal_apply,apply_ite,ite_mul]
  have he : CStarMatrix.ofMatrix (fun j k => finiteCompressionContinuous v (x j k))=
      ∑ i,star (diagonalCopies m (v i))*x*diagonalCopies m (v i) := by
    ext j k
    change (∑ i,star (v i)*x j k*v i)=matrixEntryLinear j k
      (∑ i,star (diagonalCopies m (v i))*x*diagonalCopies m (v i))
    rw [map_sum]
    change (∑ i,star (v i)*x j k*v i)=
      ∑ i,(star (diagonalCopies m (v i))*x*diagonalCopies m (v i)) j k
    simp only [he_i]
  rw [he]
  exact Finset.sum_nonneg fun i _ => star_left_conjugate_nonneg hx (diagonalCopies m (v i))

end

end

end WeakPureInfiniteness
end

end OAI
