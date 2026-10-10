import Mathlib
import OAI.Analysis.Commutator.FreeBlockTensor4

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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

include hcolors hgen in
theorem freeLevelIsHilbertSum : IsHilbertSum ℂ
    (fun n => Completion (endpointTensor t S i j n)) (levelEmbedding t S hfree hij) :=
  IsHilbertSum.mk (levelFamily_orthogonal t S hfree hij)
    (le_of_eq (total_levels t S hfree hij hcolors hgen).symm)

include hfree hij hcolors hgen in
def freeLevelSum : t.functional.GNS ≃ₗᵢ[ℂ]
    lp (fun n => Completion (endpointTensor t S i j n)) 2 :=
  (freeLevelIsHilbertSum t S hfree hij hcolors hgen).linearIsometryEquiv

@[simp] lemma freeLevelSum_symm_single (n : ℕ)
    (x : Completion (endpointTensor t S i j n)) :
    (freeLevelSum t S hfree hij hcolors hgen).symm (lp.single 2 n x) =
      levelEmbedding t S hfree hij n x :=
  IsHilbertSum.linearIsometryEquiv_symm_apply_single
    (freeLevelIsHilbertSum t S hfree hij hcolors hgen) x

end Kadison.FreeBlocks
end

end OAI
